// ==============================================================================
// AnalysisState: Salsa database + open file tracking
// ==============================================================================
//
// Wraps the Salsa RootDatabase and TypeAliasRegistry together with per-file
// cached analysis results. The LSP server holds this behind a Mutex because
// rnix::Root is !Send + !Sync and all analysis must run on a single thread
// (via spawn_blocking).

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use lang_ast::{
    module_and_source_maps, Expr, ExprId, Literal, Module, ModuleIndices, ModuleScopes,
    ModuleSourceMap, NameId, NameResolution, NixFile, RootDatabase,
};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::imports::resolve_imports;
use lang_check::{CheckResult, InferenceResult};
use lang_ty::OutputTy;
use smol_str::SmolStr;

use crate::convert::LineIndex;
use crate::project_config::ProjectConfig;

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
}

impl FileAnalysis {
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
    pub registry: TypeAliasRegistry,
    /// Cached per-file analysis, keyed by the canonical path we give to Salsa.
    pub files: HashMap<PathBuf, FileAnalysis>,
    /// Project-level tix.toml configuration (if discovered).
    pub project_config: Option<ProjectConfig>,
    /// Directory containing the tix.toml file (for resolving relative paths).
    pub config_dir: Option<PathBuf>,
}

impl AnalysisState {
    pub fn new(registry: TypeAliasRegistry) -> Self {
        Self {
            db: RootDatabase::default(),
            registry,
            files: HashMap::new(),
            project_config: None,
            config_dir: None,
        }
    }

    /// Update file contents and re-run analysis. Returns the cached analysis
    /// and a timing breakdown of each pipeline phase.
    pub fn update_file(&mut self, path: PathBuf, contents: String) -> (&FileAnalysis, AnalysisTiming) {
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

        // -- Phase 3: Import resolution --
        let t0 = Instant::now();
        let mut in_progress = HashSet::new();
        let mut cache = HashMap::new();
        let import_resolution = resolve_imports(
            &self.db,
            nix_file,
            &module,
            &name_res,
            &self.registry,
            &mut in_progress,
            &mut cache,
        );
        // TODO: surface import_resolution.errors as LSP diagnostics.

        let import_targets = import_resolution.targets;

        // Build name→import mapping: for each let-binding or attrset field
        // whose value expression is a resolved import, record the name→path link.
        // This powers Select-through-import navigation (e.g. `x.child` where
        // `x = import ./foo.nix` jumps to `child` in foo.nix).
        //
        // We chase through Apply chains because `import ./foo.nix { ... }` desugars
        // to Apply(Apply(import, ./foo.nix), { ... }) — the outer Apply isn't in
        // import_targets, but its inner function is.
        let file_dir = path.parent().map(|p| p.to_path_buf());
        let mut name_to_import = HashMap::new();
        for group in grouped.iter() {
            for typedef in group {
                // First try the recognized `import ./path` pattern via Apply chain.
                let target = chase_import_target(&module, &import_targets, typedef.expr())
                    // Fallback: scan the binding's expression subtree for a path literal.
                    // This covers patterns like `pkgs.callPackage ./foo.nix { }` where the
                    // path literal appears as an argument but isn't a direct `import`.
                    .or_else(|| {
                        let dir = file_dir.as_deref()?;
                        find_path_literal_target(&module, typedef.expr(), dir)
                    });
                if let Some(path) = target {
                    log::debug!(
                        "name_to_import: {} -> {}",
                        module[typedef.name()].text,
                        path.display()
                    );
                    name_to_import.insert(typedef.name(), path);
                }
            }
        }

        // Resolve context args for this file from the project's tix.toml.
        let context_args =
            if let (Some(ref cfg), Some(ref dir)) = (&self.project_config, &self.config_dir) {
                crate::project_config::resolve_context_for_file(&path, cfg, dir, &mut self.registry)
                    .unwrap_or_else(|e| {
                        log::warn!("Failed to resolve context for {}: {e}", path.display());
                        HashMap::new()
                    })
            } else {
                HashMap::new()
            };

        // Pre-convert context args to OutputTy for the LSP to use as a fallback
        // when the root lambda doesn't explicitly destructure a name.
        let context_arg_types: HashMap<SmolStr, OutputTy> = context_args
            .iter()
            .map(|(name, parsed_ty)| {
                let output_ty = crate::ty_nav::parsed_ty_to_output_ty(parsed_ty, &self.registry, 0);
                (name.clone(), output_ty)
            })
            .collect();
        let t_imports = t0.elapsed();

        // -- Phase 4: Type inference --
        let t0 = Instant::now();
        let check_result = lang_check::check_file_collecting(
            &self.db,
            nix_file,
            &self.registry,
            import_resolution.types,
            context_args,
        );
        let t_check = t0.elapsed();

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

    pub fn get_file(&self, path: &PathBuf) -> Option<&FileAnalysis> {
        self.files.get(path)
    }

    /// Replace the type alias registry and re-analyze all open files.
    /// Used when stubs configuration changes at runtime.
    pub fn reload_registry(&mut self, registry: TypeAliasRegistry) {
        self.registry = registry;

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
}
