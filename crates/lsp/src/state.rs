// ==============================================================================
// AnalysisState: open file tracking + type alias registry
// ==============================================================================
//
// Wraps the TypeAliasRegistry together with per-file cached analysis results.
// The LSP server holds this behind a Mutex because rnix::Root is !Send + !Sync
// and all analysis must run on a single thread (via spawn_blocking).

use rustc_hash::FxHashMap as HashMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use lang_ast::{
    Expr, ExprId, GroupedDefs, Literal, Module, ModuleIndices, ModuleScopes, ModuleSourceMap,
    NameId, NameResolution,
};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::coordinator::{InferenceCoordinator, SyntaxProvider, TypeofLookup};
#[cfg(any(test, feature = "test_support"))]
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use lang_check::imports::{import_errors_to_diagnostics, resolve_import_types};
#[cfg(test)]
use lang_check::InferenceResult;
use lang_check::{CheckResult, SyntaxBundle};
use lang_ty::OutputTy;
use smol_str::SmolStr;

use crate::convert::LineIndex;
use crate::project_config::ProjectConfig;

// ==============================================================================
// FileSnapshot: lock-free handler-accessible data
// ==============================================================================
//
// Request handlers read from FileSnapshot via DashMap — never locking the
// analysis mutex. The analysis loop is the sole writer: it publishes SyntaxData
// immediately after the cheap syntax phases (parse, lower, nameres), then adds
// InferenceData after type inference completes.

/// Syntax-level data. Always present once a file has been analyzed at least once.
/// All fields come from the same analysis pass and are internally consistent.
#[derive(Clone)]
pub struct SyntaxData {
    pub parsed: rnix::Parse<rnix::Root>,
    pub line_index: LineIndex,
    pub module: Module,
    pub module_indices: ModuleIndices,
    pub source_map: ModuleSourceMap,
    pub name_res: NameResolution,
    pub scopes: ModuleScopes,
    pub import_targets: HashMap<ExprId, PathBuf>,
    pub name_to_import: HashMap<NameId, PathBuf>,
    pub context_arg_types: HashMap<SmolStr, OutputTy>,
    /// Arena that owns all TyRef indices inside `context_arg_types`. These two
    /// fields must always be kept in sync — TyRef values from context_arg_types
    /// are only valid when indexed against this arena.
    pub context_arg_arena: Arc<lang_ty::TypeArena>,
}

/// Type inference results from a completed analysis pass.
#[derive(Clone)]
pub struct InferenceData {
    pub check_result: CheckResult,
}

/// Complete snapshot for a file. Stored in DashMap for lock-free handler access.
pub struct FileSnapshot {
    pub syntax: SyntaxData,
    pub inference: Option<InferenceData>,
}

impl FileSnapshot {
    /// Get inference even if stale (for graceful degradation).
    pub fn any_inference(&self) -> Option<&InferenceData> {
        self.inference.as_ref()
    }

    /// Convenience: get the InferenceResult if any inference data is available.
    pub fn inference_result(&self) -> Option<&lang_check::InferenceResult> {
        self.any_inference()
            .and_then(|inf| inf.check_result.inference.as_ref())
    }
}

/// Intermediate data from Phase A (syntax) needed by Phase B (imports).
/// All fields are owned values — safe to hold across mutex releases.
pub struct SyntaxIntermediate {
    pub path: PathBuf,
    pub module: Module,
    pub module_indices: ModuleIndices,
    pub name_res: NameResolution,
    pub scopes: ModuleScopes,
    pub grouped_defs: GroupedDefs,
    pub source_map: ModuleSourceMap,
    pub parsed: rnix::Parse<rnix::Root>,
    pub line_index: LineIndex,
    pub registry: Arc<TypeAliasRegistry>,
    pub context_args: Arc<HashMap<SmolStr, comment_parser::ParsedTy>>,
    pub context_arg_types: HashMap<SmolStr, OutputTy>,
    pub context_arg_arena: Arc<lang_ty::TypeArena>,
    pub rss_limit_mb: Option<f64>,
}

/// LSP-specific inference inputs. Wraps the shared `lang_check::InferenceInputs`
/// plus the import targets the analysis loop records as dependency edges.
/// (Snapshot data — parse tree, line index, source map — is published to the
/// DashMap during phase A and doesn't need to ride along here.)
pub struct LspInferenceInputs {
    pub core: lang_check::InferenceInputs,
    pub import_targets: HashMap<ExprId, PathBuf>,
}

/// Run type inference using precomputed syntax data. Does not need the
/// analysis mutex. Returns the check result and timing.
///
/// Delegates to `lang_check::run_inference()` for the actual work.
pub fn run_inference(inputs: &LspInferenceInputs) -> (CheckResult, Duration) {
    let t0 = Instant::now();
    let check_result = lang_check::run_inference(&inputs.core);
    let elapsed = t0.elapsed();
    (check_result, elapsed)
}

// ==============================================================================
// LspSyntaxProvider: reads .nix files from disk for demand-driven inference
// ==============================================================================
//
// When the LSP needs to infer a file that isn't open (e.g. an import target),
// this provider reads the file from disk, runs the syntax pipeline, and returns
// the syntax bundle needed by `InferenceCoordinator::demand_file()`.

/// Syntax provider for the LSP's demand-driven import resolution.
/// Reads .nix files from disk and runs the syntax pipeline directly.
///
/// Includes optional project config so that demand-inferred files get their
/// context_args resolved from tix.toml (e.g. `@callpackage` context for
/// files matching `pkgs/**/*.nix`). Without this, function parameters in
/// callPackage targets are unconstrained and return types resolve to `?`.
///
/// Config fields are behind a Mutex because the provider is created eagerly
/// (before `initialize()` sets the project config). Call `update_config()`
/// when the project config becomes available or changes.
pub struct LspSyntaxProvider {
    /// Behind a Mutex so we can call `Arc::make_mut` for lazy context loading.
    registry: parking_lot::Mutex<Arc<TypeAliasRegistry>>,
    /// Project config + config dir, updated via `update_config()` after
    /// `initialize()` discovers tix.toml.
    config: parking_lot::Mutex<(
        Option<crate::project_config::ProjectConfig>,
        Option<PathBuf>,
    )>,
}

impl LspSyntaxProvider {
    pub fn new(registry: Arc<TypeAliasRegistry>) -> Self {
        Self {
            registry: parking_lot::Mutex::new(registry),
            config: parking_lot::Mutex::new((None, None)),
        }
    }

    /// Update the project config after `initialize()` discovers tix.toml.
    pub fn update_config(
        &self,
        project_config: Option<crate::project_config::ProjectConfig>,
        config_dir: Option<PathBuf>,
    ) {
        *self.config.lock() = (project_config, config_dir);
    }
}

impl SyntaxProvider for LspSyntaxProvider {
    fn syntax_for_file(&self, path: &Path) -> Option<SyntaxBundle> {
        let contents = std::fs::read_to_string(path).ok()?;
        let r = lang_ast::run_syntax_pipeline_for_file(path, &contents);

        // Resolve context_args from tix.toml so demand-inferred files
        // get the same parameter typing as files opened in the editor.
        let (context_args, registry) = {
            let mut reg = self.registry.lock();
            let cfg = self.config.lock();
            let context_args = if let (Some(ref project_cfg), Some(ref dir)) = (&cfg.0, &cfg.1) {
                crate::project_config::resolve_context_for_file(
                    path,
                    project_cfg,
                    dir,
                    Arc::make_mut(&mut reg),
                )
                .unwrap_or_default()
            } else {
                Arc::default()
            };
            (context_args, Arc::clone(&reg))
        };

        Some(SyntaxBundle {
            path: path.to_path_buf(),
            module: r.module,
            module_indices: r.module_indices,
            name_res: r.name_res,
            grouped_defs: r.grouped_defs,
            registry,
            context_args,
        })
    }
}

// ==============================================================================
// resolve_imports_phase_b: demand-driven import resolution (free function)
// ==============================================================================

/// Phase B import resolution with demand-driven inference for unopened files.
///
/// Uses the coordinator cache first (fast path for already-analyzed files),
/// then falls back to `demand_file()` which reads from disk and infers on
/// demand. This function does NOT require the analysis state lock.
pub fn resolve_imports_phase_b(
    coordinator: &InferenceCoordinator,
    syntax_provider: Option<&LspSyntaxProvider>,
    intermediate: &SyntaxIntermediate,
) -> (
    LspInferenceInputs,
    HashMap<ExprId, PathBuf>,
    HashMap<NameId, PathBuf>,
    Duration,
) {
    let t0 = Instant::now();

    let base_dir = intermediate
        .path
        .parent()
        .unwrap_or(std::path::Path::new("/"));

    // Resolve imports using demand-driven lookup: try cache first, then
    // infer from disk via demand_file().
    let import_resolution = resolve_import_types(
        &intermediate.module,
        &intermediate.name_res,
        base_dir,
        |dep_path| {
            // Fast path: already in the coordinator cache.
            if let Some(ty) = coordinator.get_signature(dep_path) {
                return Some(ty);
            }
            // Demand-driven: parse + infer the dependency from disk.
            let provider = syntax_provider?;
            let result = coordinator.demand_file(dep_path, provider)?;
            result.signature.map(|s| s.root_ty)
        },
        Some(&intermediate.registry),
    );

    let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

    let import_targets = import_resolution.targets;

    let file_dir = intermediate.path.parent().map(|p| p.to_path_buf());
    let name_to_import = build_name_to_import(
        &intermediate.module,
        &import_targets,
        &intermediate.grouped_defs,
        file_dir.as_deref(),
    );

    let import_duration = t0.elapsed();

    // Scan doc comments for cross-file type references and resolve them.
    // typeof lookups are cache-only here: demanding a whole file for an
    // annotation is deferred until that file is opened or warmed up.
    let type_imports = coordinator.resolve_type_imports(
        &intermediate.path,
        &intermediate.module,
        &intermediate.module_indices.binding_expr,
        syntax_provider.map(|p| p as &dyn SyntaxProvider),
        TypeofLookup::CacheOnly,
    );
    let mut import_diagnostics = import_diagnostics;
    import_diagnostics.extend(import_errors_to_diagnostics(&type_imports.errors));
    let imported_type_exports = type_imports.imported_type_exports;
    let typeof_import_types = type_imports.typeof_import_types;

    let inference_inputs = LspInferenceInputs {
        core: lang_check::InferenceInputs {
            module: intermediate.module.clone(),
            module_indices: intermediate.module_indices.clone(),
            name_res: intermediate.name_res.clone(),
            grouped_defs: intermediate.grouped_defs.clone(),
            registry: intermediate.registry.clone(),
            import_types: import_resolution.types,
            import_diagnostics,
            context_args: intermediate.context_args.clone(),
            rss_limit_mb: intermediate.rss_limit_mb,
            file_path: Some(intermediate.path.clone()),
            imported_type_exports,
            typeof_import_types,
            file_base_dir: file_dir.clone(),
        },
        import_targets: import_targets.clone(),
    };

    (
        inference_inputs,
        import_targets,
        name_to_import,
        import_duration,
    )
}

#[cfg(any(test, feature = "test_support"))]
impl FileAnalysis {
    /// Convert a FileAnalysis into a FileSnapshot for test harnesses.
    pub fn to_snapshot(&self) -> FileSnapshot {
        FileSnapshot {
            syntax: SyntaxData {
                parsed: self.parsed.clone(),
                line_index: self.line_index.clone(),
                module: self.module.clone(),
                module_indices: self.module_indices.clone(),
                source_map: self.source_map.clone(),
                name_res: self.name_res.clone(),
                scopes: self.scopes.clone(),
                import_targets: self.import_targets.clone(),
                name_to_import: self.name_to_import.clone(),
                context_arg_types: self.context_arg_types.clone(),
                context_arg_arena: Arc::clone(&self.context_arg_arena),
            },
            inference: Some(InferenceData {
                check_result: self.check_result.clone(),
            }),
        }
    }
}

/// Cached analysis output for a single open file.
#[cfg(any(test, feature = "test_support"))]
pub struct FileAnalysis {
    /// Source text used for this analysis pass. Stored so that
    /// `reload_registry` and `ReanalyzeFile` can re-run analysis without
    /// reading from disk (which might miss unsaved editor changes).
    pub source_text: Arc<str>,
    pub line_index: LineIndex,
    /// Cached parse result. Call `.tree()` to get an rnix::Root.
    /// We store the Parse (which contains the Send-safe green tree) rather
    /// than the Root directly because Root is !Send.
    pub parsed: rnix::Parse<rnix::Root>,
    pub module: Module,
    pub module_indices: ModuleIndices,
    pub source_map: ModuleSourceMap,
    pub name_res: NameResolution,
    pub scopes: ModuleScopes,
    pub check_result: CheckResult,
    /// Maps ExprIds of import sub-expressions (Apply, Reference, Literal)
    /// to the resolved target path. For jumping from `import ./foo.nix` to the file.
    pub import_targets: HashMap<ExprId, PathBuf>,
    /// Maps NameIds bound to import expressions to the target path.
    /// For jumping through Selects: `x.child` where `x = import ./foo.nix`.
    pub name_to_import: HashMap<NameId, PathBuf>,
    /// Resolved context arg types from tix.toml, converted to OutputTy.
    /// Used as a fallback by `get_module_config_type` when the root lambda's
    /// pattern doesn't explicitly destructure a name (e.g. `{ pkgs, ... }:`
    /// without `config` — the `config :: NixosConfig` context arg still
    /// provides field information for attrpath key hover/completion).
    pub context_arg_types: HashMap<SmolStr, OutputTy>,
    /// Arena owning all TyRef indices embedded in `context_arg_types`.
    pub context_arg_arena: Arc<lang_ty::TypeArena>,
}

#[cfg(any(test, feature = "test_support"))]
impl FileAnalysis {
    #[cfg(test)]
    pub fn inference(&self) -> Option<&InferenceResult> {
        self.check_result.inference.as_ref()
    }
}

/// Timing breakdown for a single `update_file` call.
pub struct AnalysisTiming {
    pub parse: Duration,
    pub lower: Duration,
    pub name_res: Duration,
    pub imports: Duration,
    pub type_check: Duration,
    pub total: Duration,
}

impl fmt::Display for AnalysisTiming {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "total {:.1}ms (parse {:.1}ms, lower {:.1}ms, nameres {:.1}ms, imports {:.1}ms, check {:.1}ms)",
            self.total.as_secs_f64() * 1000.0,
            self.parse.as_secs_f64() * 1000.0,
            self.lower.as_secs_f64() * 1000.0,
            self.name_res.as_secs_f64() * 1000.0,
            self.imports.as_secs_f64() * 1000.0,
            self.type_check.as_secs_f64() * 1000.0,
        )
    }
}

/// All mutable state for the LSP's analysis pipeline.
pub struct AnalysisState {
    pub registry: Arc<TypeAliasRegistry>,
    /// Cached per-file analysis, keyed by canonical path. Test-only: the
    /// production server reads exclusively from the snapshots DashMap; unit
    /// tests drive analysis through `update_file` and read back snapshots.
    #[cfg(any(test, feature = "test_support"))]
    pub files: HashMap<PathBuf, FileAnalysis>,
    /// Project-level tix.toml configuration (if discovered).
    pub project_config: Option<ProjectConfig>,
    /// Directory containing the tix.toml file (for resolving relative paths).
    pub config_dir: Option<PathBuf>,

    /// Shared inference coordinator: caches file signatures (root types),
    /// tracks import dependencies, and handles invalidation cascading.
    /// Replaces the previous ephemeral_stubs / import_dependents / import_forward
    /// fields with a unified interface shared with the CLI.
    ///
    /// Wrapped in `Arc` so the analysis loop can use it outside the state lock
    /// for demand-driven import resolution.
    pub coordinator: Arc<InferenceCoordinator>,
    /// RSS limit in MB for inference. When process RSS exceeds this, inference
    /// bails out with partial results to prevent OOM crashes from RLIMIT_AS.
    pub rss_limit_mb: Option<f64>,
}

impl AnalysisState {
    pub fn new(registry: TypeAliasRegistry) -> Self {
        Self {
            registry: Arc::new(registry),
            #[cfg(any(test, feature = "test_support"))]
            files: HashMap::default(),
            project_config: None,
            config_dir: None,
            coordinator: Arc::new(InferenceCoordinator::new()),
            rss_limit_mb: None,
        }
    }

    /// Resolve context args for a file from the project's tix.toml config.
    fn resolve_context_args(
        &mut self,
        path: &Path,
    ) -> Arc<HashMap<SmolStr, comment_parser::ParsedTy>> {
        if let (Some(ref cfg), Some(ref dir)) = (&self.project_config, &self.config_dir) {
            crate::project_config::resolve_context_for_file(
                path,
                cfg,
                dir,
                Arc::make_mut(&mut self.registry),
            )
            .unwrap_or_else(|e| {
                log::warn!("Failed to resolve context for {}: {e}", path.display());
                Arc::default()
            })
        } else {
            Arc::default()
        }
    }

    /// Update file contents and re-run analysis. Returns the cached analysis
    /// and a timing breakdown of each pipeline phase.
    ///
    /// Uses cache-only import resolution (no demand-driven inference) — imported
    /// files must already be in the coordinator cache for their types to be
    /// available. The production analysis loop in `server.rs` uses
    /// `resolve_imports_phase_b()` instead, which adds demand-driven inference
    /// for unopened dependencies.
    // Only tests drive analysis through this synchronous path — the
    // production loop uses the phase A/B/C split, and reload_registry queues
    // ReanalyzeFile events instead of re-checking inline.
    #[cfg(any(test, feature = "test_support"))]
    pub fn update_file(
        &mut self,
        path: PathBuf,
        contents: String,
    ) -> (&FileAnalysis, AnalysisTiming) {
        self.update_file_inner(path, contents)
    }

    #[cfg(any(test, feature = "test_support"))]
    fn update_file_inner(
        &mut self,
        path: PathBuf,
        contents: String,
    ) -> (&FileAnalysis, AnalysisTiming) {
        // Path is expected to be pre-canonicalized by uri_to_path() at the LSP boundary.
        let t_total = Instant::now();
        // One shared buffer for line_index + source_text.
        let contents: Arc<str> = contents.into();

        // -- Phase 1: Parse --
        let t0 = Instant::now();
        let line_index = LineIndex::new(Arc::clone(&contents));
        let parsed = rnix::Root::parse(&contents);
        let t_parse = t0.elapsed();

        // -- Phase 2: Lower to Tix AST + name resolution --
        let t0 = Instant::now();
        let r = lang_ast::run_syntax_pipeline_for_file(&path, &contents);
        let t_lower = t0.elapsed();

        // -- Phase 3: Import resolution (stubs-based, O(1) lookup) --
        let t0 = Instant::now();
        let base_dir = path.parent().unwrap_or(std::path::Path::new("/"));
        let import_resolution = self.coordinator.resolve_imports(
            &r.module,
            &r.name_res,
            base_dir,
            Some(&self.registry),
        );

        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        let import_targets = import_resolution.targets;

        let file_dir = path.parent().map(|p| p.to_path_buf());
        let name_to_import = build_name_to_import(
            &r.module,
            &import_targets,
            &r.grouped_defs,
            file_dir.as_deref(),
        );

        let context_args = self.resolve_context_args(&path);
        let (context_arg_types, context_arg_arena) =
            crate::ty_nav::convert_context_args(&context_args, &self.registry);
        let t_imports = t0.elapsed();

        // -- Phase 4: Type inference --
        let t0 = Instant::now();
        let mut check_result = lang_check::CheckBuilder::from_precomputed(
            r.module.clone(),
            r.name_res.clone(),
            r.module_indices.clone(),
            r.grouped_defs.clone(),
            Arc::clone(&self.registry),
            import_resolution.types,
            context_args,
        )
        .rss_limit(self.rss_limit_mb)
        .run();
        let t_check = t0.elapsed();

        // Merge import resolution diagnostics into the check result so they
        // appear in the editor alongside type-checking diagnostics.
        check_result.diagnostics.extend(import_diagnostics);

        // If inference timed out, identify which bindings are incomplete
        // and include them in the diagnostic for actionable feedback.
        if check_result.bailed_out {
            let missing_bindings: Vec<SmolStr> = r
                .module
                .names()
                .filter(|(_, name)| {
                    matches!(
                        name.kind,
                        lang_ast::NameKind::LetIn
                            | lang_ast::NameKind::RecAttrset
                            | lang_ast::NameKind::PlainAttrset
                    )
                })
                .filter(|(id, _)| {
                    check_result
                        .inference
                        .as_ref()
                        .is_none_or(|inf| inf.name_ty_map.get(*id).is_none())
                })
                .map(|(_, name)| name.text.clone())
                .collect();
            check_result.diagnostics.push(TixDiagnostic {
                at_expr: r.module.entry_expr,
                kind: TixDiagnosticKind::InferenceAborted { missing_bindings },
            });
        }

        let t_total = t_total.elapsed();

        self.files.insert(
            path.clone(),
            FileAnalysis {
                source_text: contents,
                line_index,
                parsed,
                module: r.module,
                module_indices: r.module_indices,
                source_map: r.source_map,
                name_res: r.name_res,
                scopes: r.scopes,
                check_result,
                import_targets,
                name_to_import,
                context_arg_types,
                context_arg_arena,
            },
        );

        let timing = AnalysisTiming {
            parse: t_parse,
            lower: t_lower,
            name_res: Duration::ZERO, // folded into lower for now
            imports: t_imports,
            type_check: t_check,
            total: t_total,
        };

        (self.files.get(&path).unwrap(), timing)
    }

    #[cfg(any(test, feature = "test_support"))]
    pub fn get_file(&self, path: &PathBuf) -> Option<&FileAnalysis> {
        self.files.get(path)
    }

    /// Phase A: Parse, lower, nameres, SCC grouping. Fast (~5-50ms).
    ///
    /// Returns a `SyntaxData` (with empty import fields) for immediate DashMap
    /// publication, plus a `SyntaxIntermediate` bundle for Phase B. The caller
    /// should release the mutex after this returns so handlers can serve
    /// requests with fresh syntax data.
    pub fn update_syntax_phase_a(
        &mut self,
        path: PathBuf,
        contents: String,
    ) -> (SyntaxData, SyntaxIntermediate, Duration) {
        let t0 = Instant::now();
        // One shared buffer for line_index + source_text.
        let contents: Arc<str> = contents.into();

        // -- Parse --
        let line_index = LineIndex::new(Arc::clone(&contents));
        let parsed = rnix::Root::parse(&contents);

        // -- Lower to Tix AST + name resolution --
        let r = lang_ast::run_syntax_pipeline_for_file(&path, &contents);

        let context_args = self.resolve_context_args(&path);
        let (context_arg_types, context_arg_arena) =
            crate::ty_nav::convert_context_args(&context_args, &self.registry);

        let syntax_duration = t0.elapsed();

        // Build intermediate first (takes ownership of original values),
        // then clone from it for syntax_data — avoids two extra clones
        // that the previous order required.
        let intermediate = SyntaxIntermediate {
            path,
            module: r.module,
            module_indices: r.module_indices,
            name_res: r.name_res,
            scopes: r.scopes,
            grouped_defs: r.grouped_defs,
            source_map: r.source_map,
            parsed,
            line_index,
            registry: Arc::clone(&self.registry),
            context_args,
            context_arg_types,
            context_arg_arena,
            rss_limit_mb: self.rss_limit_mb,
        };

        // SyntaxData with empty import fields — handlers get fresh syntax
        // immediately, import data is filled in after Phase B.
        let syntax_data = SyntaxData {
            parsed: intermediate.parsed.clone(),
            line_index: intermediate.line_index.clone(),
            module: intermediate.module.clone(),
            module_indices: intermediate.module_indices.clone(),
            source_map: intermediate.source_map.clone(),
            name_res: intermediate.name_res.clone(),
            scopes: intermediate.scopes.clone(),
            import_targets: HashMap::default(),
            name_to_import: HashMap::default(),
            context_arg_types: intermediate.context_arg_types.clone(),
            context_arg_arena: Arc::clone(&intermediate.context_arg_arena),
        };

        (syntax_data, intermediate, syntax_duration)
    }

    /// Phase B: Import resolution (passive, cache-only lookup).
    ///
    /// Uses the coordinator's cache only — does NOT demand-infer unopened files.
    /// Kept for `update_file_inner` (used by unit tests). The production analysis
    /// loop uses the free function `resolve_imports_phase_b()` which adds
    /// demand-driven inference.
    #[cfg(test)]
    pub fn update_syntax_phase_b(
        &mut self,
        intermediate: &SyntaxIntermediate,
    ) -> (
        LspInferenceInputs,
        HashMap<ExprId, PathBuf>,
        HashMap<NameId, PathBuf>,
        Duration,
    ) {
        let t0 = Instant::now();

        let base_dir = intermediate
            .path
            .parent()
            .unwrap_or(std::path::Path::new("/"));
        let import_resolution = self.coordinator.resolve_imports(
            &intermediate.module,
            &intermediate.name_res,
            base_dir,
            Some(&intermediate.registry),
        );

        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        let import_targets = import_resolution.targets;

        let file_dir = intermediate.path.parent().map(|p| p.to_path_buf());
        let name_to_import = build_name_to_import(
            &intermediate.module,
            &import_targets,
            &intermediate.grouped_defs,
            file_dir.as_deref(),
        );

        let import_duration = t0.elapsed();

        let inference_inputs = LspInferenceInputs {
            core: lang_check::InferenceInputs {
                module: intermediate.module.clone(),
                module_indices: intermediate.module_indices.clone(),
                name_res: intermediate.name_res.clone(),
                grouped_defs: intermediate.grouped_defs.clone(),
                registry: intermediate.registry.clone(),
                import_types: import_resolution.types,
                import_diagnostics,
                context_args: intermediate.context_args.clone(),
                rss_limit_mb: intermediate.rss_limit_mb,
                file_path: Some(intermediate.path.clone()),
                imported_type_exports: HashMap::default(),
                typeof_import_types: HashMap::default(),
                file_base_dir: file_dir.clone(),
            },
            import_targets: import_targets.clone(),
        };

        (
            inference_inputs,
            import_targets,
            name_to_import,
            import_duration,
        )
    }

    /// Store or update the file signature in the coordinator cache.
    /// Returns `true` if the type actually changed (callers use this to decide
    /// whether to trigger dependent re-analysis).
    pub fn update_ephemeral_stub(&mut self, path: &Path, root_ty: lang_ty::OwnedTy) -> bool {
        self.coordinator
            .set_signature(path, lang_check::FileSignature { root_ty })
    }

    /// Record the import dependencies for a file via the coordinator.
    pub fn record_import_deps(&mut self, importer: &Path, imported: &[PathBuf]) {
        self.coordinator.record_deps(importer, imported);
    }

    /// Return the set of files that import the given path (its dependents).
    pub fn get_dependents(&self, path: &Path) -> Vec<PathBuf> {
        self.coordinator.get_dependents(path)
    }

    /// Remove the file's signature from the coordinator (called on `didClose`).
    /// Returns the paths of files that depended on this stub.
    pub fn remove_ephemeral_stub(&mut self, path: &Path) -> Vec<PathBuf> {
        self.coordinator.remove_signature(path)
    }

    /// Replace the type alias registry and clear cached signatures. Callers
    /// queue ReanalyzeFile events for the open files (enumerated from the
    /// snapshots map) so the re-check runs in the analysis loop rather than
    /// synchronously under the state mutex.
    pub fn reload_registry(&mut self, registry: TypeAliasRegistry) {
        self.registry = Arc::new(registry);
        self.coordinator.clear();
    }
}

/// Build a name→import-path mapping from grouped definitions and import targets.
///
/// For each let-binding or attrset field whose value expression is a resolved
/// import, records the name→path link. This powers Select-through-import
/// navigation (e.g. `x.child` where `x = import ./foo.nix` jumps to `child`
/// in foo.nix).
pub(crate) fn build_name_to_import(
    module: &Module,
    import_targets: &HashMap<ExprId, PathBuf>,
    grouped_defs: &GroupedDefs,
    file_dir: Option<&Path>,
) -> HashMap<NameId, PathBuf> {
    let mut name_to_import = HashMap::default();
    for group in grouped_defs.iter() {
        for typedef in group {
            let target =
                chase_import_target(module, import_targets, typedef.expr()).or_else(|| {
                    let dir = file_dir?;
                    find_path_literal_target(module, typedef.expr(), dir)
                });
            if let Some(path) = target {
                // Canonicalize once here so per-request consumers (e.g.
                // import_nav's pass-through scans) can compare directly
                // instead of canonicalizing per element.
                let path = path.canonicalize().unwrap_or(path);
                name_to_import.insert(typedef.name(), path);
            }
        }
    }
    name_to_import
}

/// Chase through Apply chains to find an import target.
///
/// `import ./foo.nix { args }` desugars to `Apply(Apply(import, ./foo.nix), { args })`.
/// The inner `Apply(import, ./foo.nix)` is in `import_targets`, but the outer Apply
/// (the expression actually bound to the name) isn't. This function walks the `fun`
/// chain of nested Applies until it finds a match in `import_targets`.
fn chase_import_target(
    module: &Module,
    import_targets: &HashMap<ExprId, PathBuf>,
    expr_id: ExprId,
) -> Option<PathBuf> {
    if let Some(path) = import_targets.get(&expr_id) {
        return Some(path.clone());
    }
    if let Expr::Apply { fun, .. } = &module[expr_id] {
        return chase_import_target(module, import_targets, *fun);
    }
    None
}

/// Scan an expression subtree for a single path literal that resolves to a Nix file.
///
/// This is a heuristic fallback for patterns like `pkgs.callPackage ./foo.nix { }`:
/// the path literal `./foo.nix` isn't part of an `import` expression that we track,
/// but it's still the most likely navigation target for the binding's fields.
///
/// Returns the resolved path only if exactly one Nix-file path literal is found
/// in the subtree, to avoid ambiguity.
fn find_path_literal_target(module: &Module, expr_id: ExprId, base_dir: &Path) -> Option<PathBuf> {
    let mut paths = Vec::new();
    collect_path_literals(module, expr_id, base_dir, &mut paths);

    if paths.len() == 1 {
        Some(paths.remove(0))
    } else {
        None
    }
}

/// Recursively collect resolved Nix-file path literals from an expression subtree.
fn collect_path_literals(
    module: &Module,
    expr_id: ExprId,
    base_dir: &Path,
    out: &mut Vec<PathBuf>,
) {
    match &module[expr_id] {
        Expr::Literal(Literal::Path(p)) => {
            if let Some(resolved) = resolve_nix_path(base_dir, p) {
                out.push(resolved);
            }
        }
        // Recurse into child expressions. We only need to cover the variants
        // that appear in typical `callPackage`-style expressions (Apply chains,
        // Select, etc.), but covering all variants is cheap and more robust.
        Expr::Apply { fun, arg } => {
            collect_path_literals(module, *fun, base_dir, out);
            collect_path_literals(module, *arg, base_dir, out);
        }
        Expr::Select { set, .. } => {
            collect_path_literals(module, *set, base_dir, out);
        }
        // Don't recurse into lambdas, let-in bodies, attrsets, etc. — those are
        // unlikely to contain the "source file" path for a callPackage-style call.
        _ => {}
    }
}

/// Resolve a Nix path string to an actual `.nix` file on disk.
///
/// Handles Nix's directory-import convention: if the path points to a directory,
/// tries `<dir>/default.nix`. Returns `None` if no matching file exists.
pub fn resolve_nix_path(base_dir: &Path, path_str: &str) -> Option<PathBuf> {
    let resolved = base_dir.join(path_str);
    let resolved = resolved.canonicalize().ok()?;

    if resolved.is_file() {
        Some(resolved)
    } else if resolved.is_dir() {
        let default = resolved.join("default.nix");
        if default.is_file() {
            default.canonicalize().ok()
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_check::aliases::TypeAliasRegistry;
    use rowan::ast::AstNode;
    use tower_lsp::lsp_types::Url;

    #[test]
    fn cached_parse_roundtrips_source_text() {
        let src = "let x = 1; in x + x";
        let path = crate::test_util::temp_path("parse_cache.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();

        let root = analysis.parsed.tree();
        assert_eq!(
            root.syntax().text().to_string(),
            src,
            "cached parse should reproduce the original source"
        );
    }

    #[test]
    fn missing_import_surfaces_as_diagnostic() {
        // Create a project with a Nix file that imports a non-existent file.
        let project = crate::test_util::TempProject::new(&[("main.nix", "import ./missing.nix")]);
        let nix_path = project.path("main.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, _timing) =
            state.update_file(nix_path.clone(), "import ./missing.nix".to_string());

        // There should be at least one diagnostic about the missing import.
        let import_diags: Vec<_> = analysis
            .check_result
            .diagnostics
            .iter()
            .filter(|d| matches!(d.kind, TixDiagnosticKind::ImportNotFound { .. }))
            .collect();
        assert!(
            !import_diags.is_empty(),
            "expected an ImportNotFound diagnostic, got: {:?}",
            analysis
                .check_result
                .diagnostics
                .iter()
                .map(|d| &d.kind)
                .collect::<Vec<_>>()
        );

        // Verify the diagnostic message includes the file name.
        let msg = import_diags[0].kind.to_string();
        assert!(
            msg.contains("missing.nix"),
            "diagnostic message should mention the missing file: {msg}"
        );
    }

    #[test]
    fn missing_import_converts_to_lsp_diagnostic() {
        // Verify the full LSP pipeline: import error -> TixDiagnostic -> LSP Diagnostic.
        let project =
            crate::test_util::TempProject::new(&[("main.nix", "import ./nonexistent.nix")]);
        let nix_path = project.path("main.nix");
        let src = "import ./nonexistent.nix".to_string();

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, _timing) = state.update_file(nix_path.clone(), src);

        let root = analysis.parsed.tree();
        let test_uri = Url::from_file_path(&nix_path).unwrap();
        let lsp_diags = crate::diagnostics::to_lsp_diagnostics(
            &analysis.check_result.diagnostics,
            &analysis.source_map,
            &analysis.line_index,
            &root,
            &test_uri,
        );

        // Should have at least one warning-level diagnostic about the import.
        let import_diags: Vec<_> = lsp_diags
            .iter()
            .filter(|d| d.message.contains("import target not found"))
            .collect();
        assert!(
            !import_diags.is_empty(),
            "expected an import-not-found LSP diagnostic, got: {:?}",
            lsp_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert_eq!(
            import_diags[0].severity,
            Some(tower_lsp::lsp_types::DiagnosticSeverity::WARNING),
            "import diagnostics should be warnings"
        );
    }

    #[test]
    fn duplicate_key_diagnostic_has_related_information() {
        // A let block with duplicate key `x` should produce a diagnostic
        // with related_information pointing to the first definition.
        let src = "let x = 1; x = 2; in x";
        let path = crate::test_util::temp_path("dup_key.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, _timing) = state.update_file(path.clone(), src.to_string());

        let root = analysis.parsed.tree();
        let test_uri = Url::from_file_path(&path).unwrap();
        let lsp_diags = crate::diagnostics::to_lsp_diagnostics(
            &analysis.check_result.diagnostics,
            &analysis.source_map,
            &analysis.line_index,
            &root,
            &test_uri,
        );

        let dup_diags: Vec<_> = lsp_diags
            .iter()
            .filter(|d| d.message.contains("duplicate key"))
            .collect();
        assert!(
            !dup_diags.is_empty(),
            "expected a duplicate key diagnostic, got: {:?}",
            lsp_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );

        let related = dup_diags[0].related_information.as_ref();
        assert!(
            related.is_some(),
            "duplicate key diagnostic should have related_information"
        );
        let related = related.unwrap();
        assert_eq!(related.len(), 1);
        assert_eq!(related[0].message, "first defined here");
        assert_eq!(related[0].location.uri, test_uri);
    }

    #[test]
    fn cyclic_import_degrades_gracefully() {
        // Create two files that import each other. With the stubs-based
        // import model, neither file has an ephemeral stub for the other,
        // so both imports resolve to ⊤ (unconstrained type variable).
        // The stubs-based model doesn't do cross-file inference cycles.
        let project = crate::test_util::TempProject::new(&[
            ("a.nix", "import ./b.nix"),
            ("b.nix", "import ./a.nix"),
        ]);
        let a_path = project.path("a.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, _timing) = state.update_file(a_path.clone(), "import ./b.nix".to_string());

        // Inference should complete without panic — cyclic imports degrade
        // gracefully because neither file has stubs for the other.
        assert!(
            analysis.check_result.inference.is_some(),
            "inference should produce results even with cyclic imports"
        );
    }

    // =========================================================================
    // Ephemeral stub and dependency tracking tests
    // =========================================================================

    #[test]
    fn record_import_deps_basic() {
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let a = PathBuf::from("/a.nix");
        let b = PathBuf::from("/b.nix");
        let c = PathBuf::from("/c.nix");

        state.record_import_deps(&a, &[b.clone(), c.clone()]);

        let b_deps = state.get_dependents(&b);
        let c_deps = state.get_dependents(&c);
        assert!(b_deps.contains(&a), "B's dependents should contain A");
        assert!(c_deps.contains(&a), "C's dependents should contain A");
    }

    #[test]
    fn record_import_deps_replaces_old() {
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let a = PathBuf::from("/a.nix");
        let b = PathBuf::from("/b.nix");
        let c = PathBuf::from("/c.nix");

        // A initially imports B.
        state.record_import_deps(&a, std::slice::from_ref(&b));
        assert!(
            state.get_dependents(&b).contains(&a),
            "B should list A as dependent"
        );

        // A's imports change to C only.
        state.record_import_deps(&a, std::slice::from_ref(&c));
        assert!(
            !state.get_dependents(&b).contains(&a),
            "B should no longer list A after deps replaced"
        );
        assert!(
            state.get_dependents(&c).contains(&a),
            "C should now list A as dependent"
        );
    }

    /// Helper: create an OwnedTy from a primitive OutputTy for tests.
    fn make_owned_ty(output_ty: OutputTy) -> lang_ty::OwnedTy {
        let mut arena = lang_ty::TypeArena::new();
        let root = arena.intern(output_ty);
        lang_ty::OwnedTy::new(Arc::new(arena), root)
    }

    #[test]
    fn update_ephemeral_stub_returns_changed() {
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let path = PathBuf::from("/test.nix");
        let ty_int = make_owned_ty(OutputTy::Primitive(lang_ty::PrimitiveTy::Int));
        let ty_string = make_owned_ty(OutputTy::Primitive(lang_ty::PrimitiveTy::String));

        // First insertion: new type, should return true.
        assert!(
            state.update_ephemeral_stub(&path, ty_int.clone()),
            "first insert should report changed"
        );

        // Same type again: should return false.
        assert!(
            !state.update_ephemeral_stub(&path, ty_int.clone()),
            "same type should report unchanged"
        );

        // Different type: should return true.
        assert!(
            state.update_ephemeral_stub(&path, ty_string),
            "different type should report changed"
        );
    }

    #[test]
    fn remove_ephemeral_stub_returns_dependents() {
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let a = PathBuf::from("/a.nix");
        let b = PathBuf::from("/b.nix");
        let ty_int = make_owned_ty(OutputTy::Primitive(lang_ty::PrimitiveTy::Int));

        // A imports B, B has an ephemeral stub.
        state.record_import_deps(&a, std::slice::from_ref(&b));
        state.update_ephemeral_stub(&b, ty_int);

        // Removing B's stub should return A as a dependent.
        let dependents = state.remove_ephemeral_stub(&b);
        assert!(
            dependents.contains(&a),
            "removing B's stub should return A as dependent"
        );
    }
}
