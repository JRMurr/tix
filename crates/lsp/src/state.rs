// ==============================================================================
// AnalysisState: Salsa database + open file tracking
// ==============================================================================
//
// Wraps the Salsa RootDatabase and TypeAliasRegistry together with per-file
// cached analysis results. The LSP server holds this behind a Mutex because
// rnix::Root is !Send + !Sync and all analysis must run on a single thread
// (via spawn_blocking).

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::{Duration, Instant};

use lang_ast::{
    module_and_source_maps, Expr, ExprId, GroupedDefs, Literal, Module, ModuleIndices,
    ModuleScopes, ModuleSourceMap, NameId, NameResolution, NixFile, RootDatabase,
};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::coordinator::{InferenceCoordinator, SyntaxProvider};
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
    pub nix_file: NixFile,
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
    pub deadline_secs: u64,
    pub rss_limit_mb: Option<f64>,
}

/// LSP-specific inference inputs. Wraps the shared `lang_check::InferenceInputs`
/// with additional fields needed for building `FileAnalysis`/`FileSnapshot`.
pub struct LspInferenceInputs {
    pub core: lang_check::InferenceInputs,
    // LSP-specific fields for FileAnalysis/FileSnapshot:
    pub nix_file: NixFile,
    pub line_index: LineIndex,
    pub parsed: rnix::Parse<rnix::Root>,
    pub source_map: ModuleSourceMap,
    pub scopes: ModuleScopes,
    pub import_targets: HashMap<ExprId, PathBuf>,
    pub name_to_import: HashMap<NameId, PathBuf>,
    pub context_arg_types: HashMap<SmolStr, OutputTy>,
    pub context_arg_arena: Arc<lang_ty::TypeArena>,
}

/// Run type inference using precomputed syntax data. Does not need the Salsa
/// database or the analysis mutex. Returns the check result and timing.
///
/// Delegates to `lang_check::run_inference()` for the actual work.
pub fn run_inference(
    inputs: &LspInferenceInputs,
    cancel_flag: Option<Arc<AtomicBool>>,
) -> (CheckResult, Duration) {
    let t0 = Instant::now();
    let check_result = lang_check::run_inference(&inputs.core, cancel_flag);
    let elapsed = t0.elapsed();
    (check_result, elapsed)
}

/// Build a `FileAnalysis` from inference inputs and check result. This is the
/// legacy path used during the transition — handlers will eventually read from
/// `FileSnapshot` instead.
pub fn build_file_analysis(inputs: LspInferenceInputs, check_result: CheckResult) -> FileAnalysis {
    FileAnalysis {
        nix_file: inputs.nix_file,
        line_index: inputs.line_index,
        parsed: inputs.parsed,
        module: inputs.core.module,
        module_indices: inputs.core.module_indices,
        source_map: inputs.source_map,
        name_res: inputs.core.name_res,
        scopes: inputs.scopes,
        check_result,
        import_targets: inputs.import_targets,
        name_to_import: inputs.name_to_import,
        context_arg_types: inputs.context_arg_types,
        context_arg_arena: inputs.context_arg_arena,
    }
}

// ==============================================================================
// LspSyntaxProvider: reads .nix files from disk for demand-driven inference
// ==============================================================================
//
// When the LSP needs to infer a file that isn't open (e.g. an import target),
// this provider reads the file from disk, parses it via its own RootDatabase
// (separate from the main LSP DB — no deadlock risk), and returns the syntax
// bundle needed by `InferenceCoordinator::demand_file()`.

/// Syntax provider for the LSP's demand-driven import resolution.
/// Reads .nix files from disk using an independent Salsa database.
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
    db: parking_lot::Mutex<RootDatabase>,
    /// Behind a Mutex so we can call `Arc::make_mut` for lazy context loading.
    registry: parking_lot::Mutex<Arc<TypeAliasRegistry>>,
    /// Project config + config dir, updated via `update_config()` after
    /// `initialize()` discovers tix.toml.
    config: parking_lot::Mutex<(
        Option<crate::project_config::ProjectConfig>,
        Option<PathBuf>,
    )>,
    deadline_secs: u64,
}

impl LspSyntaxProvider {
    pub fn new(registry: Arc<TypeAliasRegistry>, deadline_secs: u64) -> Self {
        Self {
            db: parking_lot::Mutex::new(RootDatabase::default()),
            registry: parking_lot::Mutex::new(registry),
            config: parking_lot::Mutex::new((None, None)),
            deadline_secs,
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
        let db = self.db.lock();
        let nix_file = db.read_file(path.to_path_buf()).ok()?;
        let (module, _source_map) = lang_ast::module_and_source_maps(&*db, nix_file);
        let module_indices = lang_ast::module_indices(&*db, nix_file);
        let name_res = lang_ast::name_resolution(&*db, nix_file);
        let grouped_defs = lang_ast::group_def(&*db, nix_file);

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
            module,
            module_indices,
            name_res,
            grouped_defs,
            registry,
            context_args,
            deadline_secs: Some(self.deadline_secs),
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
    cancel_flag: Option<Arc<AtomicBool>>,
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
            let result = coordinator.demand_file(dep_path, provider, cancel_flag.clone())?;
            result.signature.map(|s| s.root_ty)
        },
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
            deadline_secs: Some(intermediate.deadline_secs),
            rss_limit_mb: intermediate.rss_limit_mb,
            file_path: Some(intermediate.path.clone()),
        },
        nix_file: intermediate.nix_file,
        line_index: intermediate.line_index.clone(),
        parsed: intermediate.parsed.clone(),
        source_map: intermediate.source_map.clone(),
        scopes: intermediate.scopes.clone(),
        import_targets: import_targets.clone(),
        name_to_import: name_to_import.clone(),
        context_arg_types: intermediate.context_arg_types.clone(),
        context_arg_arena: Arc::clone(&intermediate.context_arg_arena),
    };

    (
        inference_inputs,
        import_targets,
        name_to_import,
        import_duration,
    )
}

impl FileAnalysis {
    /// Convert a FileAnalysis into a FileSnapshot. Used by tests and the
    /// transitional period where both representations coexist.
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
pub struct FileAnalysis {
    pub nix_file: NixFile,
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
    pub db: RootDatabase,
    pub registry: Arc<TypeAliasRegistry>,
    /// Cached per-file analysis, keyed by the canonical path we give to Salsa.
    pub files: HashMap<PathBuf, FileAnalysis>,
    /// Project-level tix.toml configuration (if discovered).
    pub project_config: Option<ProjectConfig>,
    /// Directory containing the tix.toml file (for resolving relative paths).
    pub config_dir: Option<PathBuf>,
    /// Inference deadline in seconds (per top-level file). Configurable via
    /// `deadline` in `tix.toml`, defaults to 10.
    pub deadline_secs: u64,

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
            db: RootDatabase::default(),
            registry: Arc::new(registry),
            files: HashMap::new(),
            project_config: None,
            config_dir: None,
            deadline_secs: 10,
            coordinator: Arc::new(InferenceCoordinator::new()),
            rss_limit_mb: None,
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
    pub fn update_file(
        &mut self,
        path: PathBuf,
        contents: String,
    ) -> (&FileAnalysis, AnalysisTiming) {
        self.update_file_inner(path, contents, None)
    }

    /// Like `update_file` but with an external cancellation flag. When the
    /// flag is set to `true` (e.g. because a newer edit arrived for the same
    /// file), type inference bails out early with partial results.
    #[cfg(test)]
    pub fn update_file_with_cancel(
        &mut self,
        path: PathBuf,
        contents: String,
        cancel_flag: Arc<AtomicBool>,
    ) -> (&FileAnalysis, AnalysisTiming) {
        self.update_file_inner(path, contents, Some(cancel_flag))
    }

    /// Shared implementation for `update_file` and `update_file_with_cancel`.
    fn update_file_inner(
        &mut self,
        path: PathBuf,
        contents: String,
        cancel_flag: Option<Arc<AtomicBool>>,
    ) -> (&FileAnalysis, AnalysisTiming) {
        // Path is expected to be pre-canonicalized by uri_to_path() at the LSP boundary.
        let t_total = Instant::now();

        // -- Phase 1: Parse --
        let t0 = Instant::now();
        let line_index = LineIndex::new(&contents);
        let parsed = rnix::Root::parse(&contents);
        let nix_file = self.db.set_file_contents(path.clone(), contents);
        let t_parse = t0.elapsed();

        // -- Phase 2: Lower to Tix AST + name resolution --
        let t0 = Instant::now();
        let (module, source_map) = module_and_source_maps(&self.db, nix_file);
        let module_indices = lang_ast::module_indices(&self.db, nix_file);
        let name_res = lang_ast::name_resolution(&self.db, nix_file);
        let scopes = lang_ast::scopes(&self.db, nix_file);
        let grouped = lang_ast::group_def(&self.db, nix_file);
        let t_lower = t0.elapsed();

        // -- Phase 3: Import resolution (stubs-based, O(1) lookup) --
        let t0 = Instant::now();
        let base_dir = path.parent().unwrap_or(std::path::Path::new("/"));
        let import_resolution = self
            .coordinator
            .resolve_imports(&module, &name_res, base_dir);

        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        let import_targets = import_resolution.targets;

        let file_dir = path.parent().map(|p| p.to_path_buf());
        let name_to_import =
            build_name_to_import(&module, &import_targets, &grouped, file_dir.as_deref());

        // Resolve context args for this file from the project's tix.toml.
        let context_args: Arc<HashMap<SmolStr, comment_parser::ParsedTy>> =
            if let (Some(ref cfg), Some(ref dir)) = (&self.project_config, &self.config_dir) {
                crate::project_config::resolve_context_for_file(
                    &path,
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
            };

        // Pre-convert context args to OutputTy for the LSP to use as a fallback
        // when the root lambda doesn't explicitly destructure a name. All entries
        // share one arena so TyRef children remain valid when traversed together.
        let mut context_arena = lang_ty::TypeArena::new();
        let context_arg_types: HashMap<SmolStr, OutputTy> = context_args
            .iter()
            .map(|(name, parsed_ty)| {
                let output_ty = crate::ty_nav::parsed_ty_to_output_ty(
                    parsed_ty,
                    &self.registry,
                    &mut context_arena,
                    0,
                );
                (name.clone(), output_ty)
            })
            .collect();
        let context_arg_arena = Arc::new(context_arena);
        let t_imports = t0.elapsed();

        // -- Phase 4: Type inference --
        // Deadline for the top-level file (configurable via `deadline` in
        // tix.toml, default 10s). If inference hangs (e.g. due to pathological
        // constraint propagation on complex files), bail out with partial
        // results rather than blocking the LSP indefinitely. The cancel flag
        // provides an additional early-exit path when a newer edit supersedes
        // this analysis.
        let t0 = Instant::now();
        let deadline = Some(Instant::now() + Duration::from_secs(self.deadline_secs));
        let mut check_result = lang_check::CheckBuilder::from_db(
            &self.db,
            nix_file,
            Arc::clone(&self.registry),
            import_resolution.types,
            context_args,
        )
        .deadline(deadline)
        .cancel_flag(cancel_flag)
        .rss_limit(self.rss_limit_mb)
        .run();
        let t_check = t0.elapsed();

        // Merge import resolution diagnostics into the check result so they
        // appear in the editor alongside type-checking diagnostics.
        check_result.diagnostics.extend(import_diagnostics);

        // If inference timed out, identify which bindings are incomplete
        // and include them in the diagnostic for actionable feedback.
        if check_result.timed_out {
            let missing_bindings: Vec<SmolStr> = module
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
                at_expr: module.entry_expr,
                kind: TixDiagnosticKind::InferenceTimeout { missing_bindings },
            });
        }

        let t_total = t_total.elapsed();

        self.files.insert(
            path.clone(),
            FileAnalysis {
                nix_file,
                line_index,
                parsed,
                module,
                module_indices,
                source_map,
                name_res,
                scopes,
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

    #[cfg(test)]
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

        // -- Parse --
        let line_index = LineIndex::new(&contents);
        let parsed = rnix::Root::parse(&contents);
        let nix_file = self.db.set_file_contents(path.clone(), contents);

        // -- Lower to Tix AST + name resolution --
        let (module, source_map) = module_and_source_maps(&self.db, nix_file);
        let module_indices = lang_ast::module_indices(&self.db, nix_file);
        let name_res = lang_ast::name_resolution(&self.db, nix_file);
        let scopes = lang_ast::scopes(&self.db, nix_file);
        let grouped = lang_ast::group_def(&self.db, nix_file);

        // Resolve context args (fast, depends only on project config).
        let context_args: Arc<HashMap<SmolStr, comment_parser::ParsedTy>> =
            if let (Some(ref cfg), Some(ref dir)) = (&self.project_config, &self.config_dir) {
                crate::project_config::resolve_context_for_file(
                    &path,
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
            };

        // All context arg types share a single arena so their TyRef children
        // remain valid when navigated together in get_module_config_type.
        let mut context_arena = lang_ty::TypeArena::new();
        let context_arg_types: HashMap<SmolStr, OutputTy> = context_args
            .iter()
            .map(|(name, parsed_ty)| {
                let output_ty = crate::ty_nav::parsed_ty_to_output_ty(
                    parsed_ty,
                    &self.registry,
                    &mut context_arena,
                    0,
                );
                (name.clone(), output_ty)
            })
            .collect();
        let context_arg_arena = Arc::new(context_arena);

        let syntax_duration = t0.elapsed();

        // Build intermediate first (takes ownership of original values),
        // then clone from it for syntax_data — avoids two extra clones
        // that the previous order required.
        let intermediate = SyntaxIntermediate {
            nix_file,
            path,
            module,
            module_indices,
            name_res,
            scopes,
            grouped_defs: grouped,
            source_map,
            parsed,
            line_index,
            registry: Arc::clone(&self.registry),
            context_args,
            context_arg_types,
            context_arg_arena,
            deadline_secs: self.deadline_secs,
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
            import_targets: HashMap::new(),
            name_to_import: HashMap::new(),
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
                deadline_secs: Some(intermediate.deadline_secs),
                rss_limit_mb: intermediate.rss_limit_mb,
                file_path: Some(intermediate.path.clone()),
            },
            nix_file: intermediate.nix_file,
            line_index: intermediate.line_index.clone(),
            parsed: intermediate.parsed.clone(),
            source_map: intermediate.source_map.clone(),
            scopes: intermediate.scopes.clone(),
            import_targets: import_targets.clone(),
            name_to_import: name_to_import.clone(),
            context_arg_types: intermediate.context_arg_types.clone(),
            context_arg_arena: Arc::clone(&intermediate.context_arg_arena),
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

    /// Replace the type alias registry and re-analyze all open files.
    /// Used when stubs configuration changes at runtime.
    pub fn reload_registry(&mut self, registry: TypeAliasRegistry) {
        self.registry = Arc::new(registry);
        self.coordinator.clear();

        // Re-analyze every open file with the new registry.
        let paths: Vec<PathBuf> = self.files.keys().cloned().collect();
        for path in paths {
            // Retrieve the current source text from the Salsa database so we
            // can re-run update_file without needing the original String.
            let contents = {
                let analysis = self.files.get(&path).unwrap();
                analysis.nix_file.contents(&self.db).to_owned()
            };
            let (_analysis, timing) = self.update_file(path.clone(), contents);
            log::info!("re-analyzed {}: {timing}", path.display());
        }
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
    let mut name_to_import = HashMap::new();
    for group in grouped_defs.iter() {
        for typedef in group {
            let target =
                chase_import_target(module, import_targets, typedef.expr()).or_else(|| {
                    let dir = file_dir?;
                    find_path_literal_target(module, typedef.expr(), dir)
                });
            if let Some(path) = target {
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
            Some(default.canonicalize().ok().unwrap_or(default))
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
        // No Salsa cycle recovery is involved — the stubs-based model
        // doesn't use Salsa for cross-file inference.
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

    #[test]
    fn update_file_with_cancel_completes_normally_when_not_cancelled() {
        // When the cancel flag is never set, analysis should complete and
        // produce valid results — identical to `update_file`.
        let src = "let x = 1; in x + x";
        let path = crate::test_util::temp_path("cancel_normal.nix");
        let cancel = Arc::new(AtomicBool::new(false));

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, timing) =
            state.update_file_with_cancel(path.clone(), src.to_string(), cancel);

        // Should have valid inference results.
        assert!(
            analysis.inference().is_some(),
            "inference should succeed when cancel flag is not set"
        );
        // Timing should be non-zero.
        assert!(
            timing.total > Duration::ZERO,
            "timing should be non-zero for completed analysis"
        );
        // Should not be marked as timed out.
        assert!(
            !analysis.check_result.timed_out,
            "should not be marked as timed out"
        );
    }

    #[test]
    fn update_file_with_cancel_aborts_when_pre_cancelled() {
        // When the cancel flag is already set before analysis begins,
        // inference should bail out immediately with partial results.
        let src = "let x = 1; in x + x";
        let path = crate::test_util::temp_path("cancel_pre.nix");
        let cancel = Arc::new(AtomicBool::new(true));

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (analysis, _timing) =
            state.update_file_with_cancel(path.clone(), src.to_string(), cancel);

        // When cancelled before inference starts, the inference engine
        // treats it like a deadline exceeded — timed_out is set to true.
        assert!(
            analysis.check_result.timed_out,
            "should be marked as timed out when cancel flag is pre-set"
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
        state.record_import_deps(&a, &[b.clone()]);
        assert!(
            state.get_dependents(&b).contains(&a),
            "B should list A as dependent"
        );

        // A's imports change to C only.
        state.record_import_deps(&a, &[c.clone()]);
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
        state.record_import_deps(&a, &[b.clone()]);
        state.update_ephemeral_stub(&b, ty_int);

        // Removing B's stub should return A as a dependent.
        let dependents = state.remove_ephemeral_stub(&b);
        assert!(
            dependents.contains(&a),
            "removing B's stub should return A as dependent"
        );
    }
}
