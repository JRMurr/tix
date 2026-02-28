// ==============================================================================
// Multi-File Import Resolution
// ==============================================================================
//
// Before inference begins for a file, we scan its AST for `import <literal-path>`
// and `callPackage <literal-path> <overrides>` patterns, recursively infer each
// target file, and build a pre-computed `ExprId -> OutputTy` map. This map is
// passed into CheckCtx so that Apply expressions matching resolved imports use
// the imported file's root type instead of the unconstrained `a -> b` from the
// builtin `import` signature.
//
// For `callPackage`, the target file's root type is a function (the package
// derivation). Since callPackage applies the dependency-injection argument, we
// peel one Lambda layer to get the return type.
//
// Type isolation: each imported file is inferred in its own CheckCtx with its
// own TypeStorage. The result is canonicalized to immutable OutputTy values.
// When the importing file interns the OutputTy, it creates fresh TyIds in its
// own storage — no cross-file mutation is possible.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstDb, Expr, ExprId, Literal, Module, NameResolution, NixFile};
use lang_ty::OutputTy;

/// Default aggregate deadline for the entire import tree (30 seconds).
/// Individual files may have their own per-file deadline (import_deadline_secs),
/// but the aggregate ensures the total wall-clock time for recursively resolving
/// all transitive imports is bounded.
const DEFAULT_AGGREGATE_DEADLINE_SECS: u64 = 30;

// ==============================================================================
// Import Scanning
// ==============================================================================

/// Scan a module's AST for `import <literal-path>` patterns.
///
/// Walks all expressions looking for Apply nodes where:
/// - `fun` is a Reference("import") that resolves to Builtin("import")
/// - `arg` is a Literal(Path(..))
///
/// Returns `(apply_expr_id, resolved_path)` pairs. Non-literal import args
/// (interpolations, variables, etc.) are silently skipped — they remain as
/// unconstrained type variables via the normal `import :: a -> b` synthesis.
pub fn scan_literal_imports(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
) -> Vec<(ExprId, PathBuf)> {
    let mut imports = Vec::new();

    for (expr_id, expr) in module.exprs() {
        let Expr::Apply { fun, arg } = expr else {
            continue;
        };

        // Check that `fun` is a reference to the builtin `import`.
        let Expr::Reference(ref name) = module[*fun] else {
            continue;
        };
        if name != "import" {
            continue;
        }
        let is_builtin_import = matches!(
            name_res.get(*fun),
            Some(ResolveResult::Builtin("import")) | None
        );
        if !is_builtin_import {
            continue;
        }

        // Check that `arg` is a literal path.
        let Expr::Literal(Literal::Path(path_str)) = &module[*arg] else {
            continue;
        };

        // Skip angle bracket search paths (e.g. `<nixpkgs>`). These require
        // NIX_PATH resolution which we don't implement yet — treating them as
        // literal path components produces nonsensical paths.
        // TODO: resolve via NIX_PATH
        if path_str.starts_with('<') {
            continue;
        }

        let resolved = base_dir.join(path_str);
        imports.push((expr_id, resolved));
    }

    imports
}

// ==============================================================================
// callPackage Scanning
// ==============================================================================

/// Check whether an ExprId refers to something named `callPackage`.
///
/// Matches two patterns:
/// - `callPackage` — a bare `Reference("callPackage")`
/// - `pkgs.callPackage` — a `Select` whose last attrpath segment is the string
///   literal `"callPackage"`
///
/// Only exact `"callPackage"` — NOT `callPackageWith` or `callPackagesWith`,
/// which have a different argument structure.
fn is_callpackage_callee(module: &Module, expr_id: ExprId) -> bool {
    match &module[expr_id] {
        Expr::Reference(name) => name == "callPackage",
        Expr::Select { attrpath, .. } => {
            if let Some(last) = attrpath.last() {
                matches!(&module[*last], Expr::Literal(Literal::String(s)) if s == "callPackage")
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Scan a module's AST for `callPackage <literal-path> <overrides>` patterns.
///
/// The Nix desugaring of `callPackage ./pkg.nix {}` is:
///   `Apply { fun: Apply { fun: callPackage, arg: ./pkg.nix }, arg: {} }`
///
/// Returns `(outer_apply_id, inner_apply_id, path_literal_expr_id, resolved_path)`.
pub(crate) fn scan_callpackage_imports(
    module: &Module,
    base_dir: &Path,
) -> Vec<(ExprId, ExprId, ExprId, PathBuf)> {
    let mut results = Vec::new();

    for (outer_id, expr) in module.exprs() {
        // outer Apply: callPackage ./path <overrides>
        let Expr::Apply {
            fun: inner_apply_id,
            arg: _,
        } = expr
        else {
            continue;
        };

        // inner Apply: callPackage ./path
        let Expr::Apply {
            fun: callee_id,
            arg: path_arg_id,
        } = &module[*inner_apply_id]
        else {
            continue;
        };

        if !is_callpackage_callee(module, *callee_id) {
            continue;
        }

        let Expr::Literal(Literal::Path(path_str)) = &module[*path_arg_id] else {
            continue;
        };

        // Skip angle bracket search paths (e.g. `<nixpkgs>`).
        // TODO: resolve via NIX_PATH
        if path_str.starts_with('<') {
            continue;
        }

        let resolved = base_dir.join(path_str);
        results.push((outer_id, *inner_apply_id, *path_arg_id, resolved));
    }

    results
}

/// Peel one Lambda layer from a type to get the return type.
///
/// `callPackage` applies the dependency-injection argument (the first parameter
/// of the package function), so we extract the body type. For non-function files
/// (e.g. a plain attrset), the type is returned as-is.
pub(crate) fn extract_return_type(ty: &OutputTy) -> OutputTy {
    match ty {
        OutputTy::Lambda { body, .. } => body.0.as_ref().clone(),
        OutputTy::Named(_, inner) => extract_return_type(&inner.0),
        other => other.clone(),
    }
}

/// Resolve a path that may point to a directory, applying Nix's convention
/// of loading `default.nix` from directories.
///
/// Returns `None` if the path is a directory with no `default.nix`.
pub(crate) fn resolve_directory_path(path: PathBuf) -> Option<PathBuf> {
    if path.is_dir() {
        let default = path.join("default.nix");
        if default.is_file() {
            Some(default.canonicalize().unwrap_or(default))
        } else {
            None
        }
    } else {
        Some(path)
    }
}

// ==============================================================================
// Import Kinds
// ==============================================================================

/// Distinguishes regular `import` from `callPackage` so the resolution loop
/// can handle both uniformly but store the result type differently.
enum ImportKind {
    /// `import <literal-path>` — the resolved type is used directly.
    Import { apply_expr_id: ExprId },
    /// `callPackage <literal-path> <overrides>` — the resolved type has one
    /// Lambda layer peeled to get the return type.
    CallPackage {
        outer_apply_id: ExprId,
        /// The inner `Apply(callPackage, path)` — registered with the raw file
        /// type so that inferring it doesn't produce spurious type errors from
        /// applying the user's `callPackage` function to a path literal.
        inner_apply_id: ExprId,
        path_literal_id: ExprId,
    },
}

// ==============================================================================
// Import Errors
// ==============================================================================

#[derive(Debug, Clone)]
pub enum ImportErrorKind {
    FileNotFound(PathBuf),
    /// Cyclic import detected — file A imports B which (transitively) imports A.
    /// TODO: A future extension could support cross-file SCCs by merging modules.
    CyclicImport(PathBuf),
    InferenceError(PathBuf, Box<crate::diagnostic::TixDiagnostic>),
}

#[derive(Debug, Clone)]
pub struct ImportError {
    pub kind: ImportErrorKind,
    /// The Apply expression in the importing file where this error occurred.
    pub at_expr: ExprId,
}

// ==============================================================================
// Import Resolution
// ==============================================================================

/// Result of resolving all imports in a file.
pub struct ImportResolution {
    /// Successfully resolved import types, keyed by the Apply ExprId in the
    /// importing file.
    pub types: HashMap<ExprId, OutputTy>,
    /// Errors encountered during import resolution.
    pub errors: Vec<ImportError>,
    /// Maps ExprIds of import sub-expressions (Apply, Reference, Literal)
    /// to the resolved target path. Used by the LSP for jump-to-definition
    /// on `import ./foo.nix` expressions.
    pub targets: HashMap<ExprId, PathBuf>,
}

// ==============================================================================
// Stubs-Based Import Resolution
// ==============================================================================

/// Resolve import types using ephemeral stubs only (no recursive inference).
///
/// For each scanned import target path:
/// 1. Records navigation targets (for goto-def) regardless of type availability
/// 2. Looks up type from `ephemeral_stubs` (inferred types of open/analyzed files)
/// 3. Falls through to ⊤ (no entry in result map → builtin `import :: a -> b`)
///
/// Also builds the `import_targets` and `name_to_import` maps for navigation.
/// This replaces the recursive `resolve_imports()` path: files are inferred
/// independently, and cross-file types come from stubs or ephemeral stubs.
pub fn resolve_import_types_from_stubs(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
    ephemeral_stubs: &HashMap<PathBuf, OutputTy>,
) -> ImportResolution {
    let literal_imports = scan_literal_imports(module, name_res, base_dir);
    let callpackage_imports = scan_callpackage_imports(module, base_dir);

    // Track which paths are already handled by regular imports so we don't
    // double-resolve files that appear in both `import ./x` and `callPackage ./x`.
    let import_paths: HashSet<PathBuf> = literal_imports
        .iter()
        .filter_map(|(_, p)| p.canonicalize().ok())
        .collect();

    let mut types = HashMap::new();
    let mut errors = Vec::new();
    let mut targets = HashMap::new();

    // ---- Literal imports ----
    for (apply_expr_id, target_path) in literal_imports {
        let target_path = target_path.canonicalize().unwrap_or(target_path);

        let target_path = match resolve_directory_path(target_path.clone()) {
            Some(p) => p,
            None => {
                // Directory exists but has no default.nix — or path not found on disk.
                // Only emit FileNotFound if the original path doesn't exist at all.
                if !target_path.exists() {
                    errors.push(ImportError {
                        kind: ImportErrorKind::FileNotFound(target_path),
                        at_expr: apply_expr_id,
                    });
                }
                continue;
            }
        };

        // Record navigation targets (Apply, fun/Reference, arg/Literal).
        if let Expr::Apply { fun, arg } = &module[apply_expr_id] {
            targets.insert(*fun, target_path.clone());
            targets.insert(*arg, target_path.clone());
        }
        targets.insert(apply_expr_id, target_path.clone());

        // Look up ephemeral stub — if found, use it; otherwise falls through
        // to the generic `import :: a -> b` builtin type.
        if let Some(stub_ty) = ephemeral_stubs.get(&target_path) {
            types.insert(apply_expr_id, stub_ty.clone());
        }
    }

    // ---- callPackage imports ----
    for (outer_apply_id, inner_apply_id, path_literal_id, target_path) in callpackage_imports {
        let target_path = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());

        // Skip if a regular import already covers this file.
        if import_paths.contains(&target_path) {
            continue;
        }

        let target_path = match resolve_directory_path(target_path.clone()) {
            Some(p) => p,
            None => {
                if !target_path.exists() {
                    errors.push(ImportError {
                        kind: ImportErrorKind::FileNotFound(target_path),
                        at_expr: outer_apply_id,
                    });
                }
                continue;
            }
        };

        // Record navigation targets.
        targets.insert(path_literal_id, target_path.clone());
        targets.insert(outer_apply_id, target_path.clone());
        targets.insert(inner_apply_id, target_path.clone());

        // Look up ephemeral stub.
        if let Some(stub_ty) = ephemeral_stubs.get(&target_path) {
            types.insert(inner_apply_id, stub_ty.clone());
            types.insert(outer_apply_id, extract_return_type(stub_ty));
        }
    }

    ImportResolution {
        types,
        errors,
        targets,
    }
}

/// Recursively resolve all literal imports and callPackage patterns in a file.
///
/// For each `import <literal-path>` or `callPackage <literal-path> <overrides>`:
/// - If the target is already being resolved (in `in_progress`), record a cyclic
///   import error.
/// - If the target was already resolved (in `cache`), reuse the cached type.
/// - Otherwise, load and infer the target file recursively, then cache the result.
///
/// For callPackage, one Lambda layer is peeled from the file's root type since
/// callPackage applies the dependency-injection argument.
///
/// The `cache` prevents re-inferring files in diamond import patterns (A imports
/// B and C, both of which import D — D is inferred only once).
#[allow(clippy::too_many_arguments)]
pub fn resolve_imports(
    db: &dyn AstDb,
    file: NixFile,
    module: &Module,
    name_res: &NameResolution,
    in_progress: &mut HashSet<PathBuf>,
    cache: &mut HashMap<PathBuf, OutputTy>,
    _import_deadline_secs: Option<u64>,
    aggregate_deadline: Option<Instant>,
    cancel_flag: Option<&Arc<AtomicBool>>,
    max_imports: Option<usize>,
) -> ImportResolution {
    // Initialize the aggregate deadline on the first call (depth 0). Recursive
    // calls pass the same deadline through, so the entire import tree shares a
    // single wall-clock budget.
    let aggregate_deadline = aggregate_deadline
        .unwrap_or_else(|| Instant::now() + Duration::from_secs(DEFAULT_AGGREGATE_DEADLINE_SECS));
    // Determine the base directory for resolving relative import paths.
    let file_path = file.path(db);
    let base_dir = file_path.parent().unwrap_or(Path::new("/"));

    // Collect both regular imports and callPackage patterns into a unified
    // work list so they share the same cache, cycle detection, and inference
    // pipeline. The only difference is how the result type is stored.
    let literal_imports = scan_literal_imports(module, name_res, base_dir);
    let callpackage_imports = scan_callpackage_imports(module, base_dir);

    // Track which paths are already handled by regular imports so we don't
    // double-infer files that appear in both `import ./x` and `callPackage ./x`.
    let import_paths: HashSet<PathBuf> = literal_imports
        .iter()
        .map(|(_, p)| p.canonicalize().unwrap_or_else(|_| p.clone()))
        .collect();

    let mut work: Vec<(ImportKind, PathBuf)> = Vec::new();

    for (apply_expr_id, target_path) in literal_imports {
        work.push((ImportKind::Import { apply_expr_id }, target_path));
    }

    for (outer_apply_id, inner_apply_id, path_literal_id, target_path) in callpackage_imports {
        let canonical = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());
        // Skip if a regular import already covers this file — importing the
        // same path via both `import` and `callPackage` would be unusual, but
        // guard against it to avoid duplicate work.
        if import_paths.contains(&canonical) {
            continue;
        }
        work.push((
            ImportKind::CallPackage {
                outer_apply_id,
                inner_apply_id,
                path_literal_id,
            },
            target_path,
        ));
    }

    let mut types = HashMap::new();
    let mut errors = Vec::new();
    let mut targets = HashMap::new();

    let depth = in_progress.len();
    let indent = "  ".repeat(depth);
    if !work.is_empty() {
        log::info!(
            "{indent}resolve_imports: {} import(s) from {}",
            work.len(),
            file_path.display(),
        );
    }

    // When there are many imports at the top level (depth 0), use the
    // parallel rayon path for a significant speedup. Below the threshold,
    // the sequential Salsa path is fine and preserves incremental memoization.
    const PARALLEL_THRESHOLD: usize = 50;
    if depth == 0 && work.len() >= PARALLEL_THRESHOLD {
        log::info!(
            "resolve_imports: {} imports exceeds parallel threshold ({}), using rayon",
            work.len(),
            PARALLEL_THRESHOLD,
        );
        return resolve_imports_parallel(
            db,
            file,
            module,
            name_res,
            &work,
            cache,
            aggregate_deadline,
            cancel_flag,
            max_imports,
        );
    }

    let mut resolved_count: usize = 0;

    for (kind, target_path) in work {
        // Check aggregate deadline and cancel flag before each import. This
        // bounds the total wall-clock time for the entire import tree,
        // preventing pathological transitive graphs from blocking the LSP.
        if Instant::now() > aggregate_deadline {
            log::warn!("{indent}  aggregate import deadline exceeded, stopping");
            break;
        }
        if cancel_flag.is_some_and(|f| f.load(Ordering::Relaxed)) {
            log::info!("{indent}  import resolution cancelled");
            break;
        }
        if max_imports.is_some_and(|cap| resolved_count >= cap) {
            log::warn!(
                "{indent}  import cap ({}) reached, remaining imports will use generic import type",
                max_imports.unwrap(),
            );
            break;
        }

        // Canonicalize the path so cycle detection and caching work correctly
        // even with symlinks or `..` components. Fall back to the raw path
        // when canonicalization fails (e.g. in-memory test databases where
        // the path doesn't exist on disk).
        let target_path = target_path.canonicalize().unwrap_or(target_path);

        // Resolve directory paths to default.nix (Nix convention).
        let target_path = match resolve_directory_path(target_path.clone()) {
            Some(p) => p,
            None => {
                let error_expr = match &kind {
                    ImportKind::Import { apply_expr_id } => *apply_expr_id,
                    ImportKind::CallPackage { outer_apply_id, .. } => *outer_apply_id,
                };
                errors.push(ImportError {
                    kind: ImportErrorKind::FileNotFound(target_path),
                    at_expr: error_expr,
                });
                continue;
            }
        };

        let target_name = target_path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| target_path.display().to_string());

        // Record navigation targets for the LSP before any cycle/cache/load
        // checks, so even failed imports get jump-to-definition support.
        match &kind {
            ImportKind::Import { apply_expr_id } => {
                if let Expr::Apply { fun, arg } = &module[*apply_expr_id] {
                    targets.insert(*fun, target_path.clone());
                    targets.insert(*arg, target_path.clone());
                }
                targets.insert(*apply_expr_id, target_path.clone());
            }
            ImportKind::CallPackage {
                outer_apply_id,
                inner_apply_id,
                path_literal_id,
            } => {
                targets.insert(*path_literal_id, target_path.clone());
                targets.insert(*outer_apply_id, target_path.clone());
                targets.insert(*inner_apply_id, target_path.clone());
            }
        }

        // Check for cycles.
        let error_expr = match &kind {
            ImportKind::Import { apply_expr_id } => *apply_expr_id,
            ImportKind::CallPackage { outer_apply_id, .. } => *outer_apply_id,
        };
        if in_progress.contains(&target_path) {
            log::info!("{indent}  {target_name}: cycle detected, skipping");
            errors.push(ImportError {
                kind: ImportErrorKind::CyclicImport(target_path),
                at_expr: error_expr,
            });
            continue;
        }

        // Check cache — use the raw file type, then apply kind-specific
        // transformation (extract_return_type for callPackage).
        if let Some(cached_ty) = cache.get(&target_path) {
            log::info!("{indent}  {target_name}: cached");
            match &kind {
                ImportKind::Import { apply_expr_id } => {
                    types.insert(*apply_expr_id, cached_ty.clone());
                }
                ImportKind::CallPackage {
                    outer_apply_id,
                    inner_apply_id,
                    ..
                } => {
                    // Register the raw file type on the inner Apply so that
                    // infer_expr short-circuits it (avoids type errors from
                    // applying the user's callPackage function to a path literal).
                    types.insert(*inner_apply_id, cached_ty.clone());
                    types.insert(*outer_apply_id, extract_return_type(cached_ty));
                }
            }
            continue;
        }

        log::info!("{indent}  {target_name}: loading...");

        // Load and infer the target file.
        let Some(target_file) = db.load_file(&target_path) else {
            log::info!("{indent}  {target_name}: file not found");
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: error_expr,
            });
            continue;
        };

        // Infer via Salsa-memoized file_root_type. Cached results return
        // instantly; only files whose contents changed trigger re-inference.
        // Cycles are handled by Salsa's cycle_result recovery.
        let t0 = Instant::now();
        // Grow the stack before recursing into file_root_type — it recurses
        // through resolve_import_types_salsa for the entire transitive import
        // graph, which can overflow the default thread stack.
        let root_ty = stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            crate::salsa_imports::file_root_type(db, target_file)
        });
        let t_infer = t0.elapsed();

        cache.insert(target_path.clone(), root_ty.clone());

        match &kind {
            ImportKind::Import { apply_expr_id } => {
                types.insert(*apply_expr_id, root_ty);
            }
            ImportKind::CallPackage {
                outer_apply_id,
                inner_apply_id,
                ..
            } => {
                types.insert(*inner_apply_id, root_ty.clone());
                types.insert(*outer_apply_id, extract_return_type(&root_ty));
            }
        }

        resolved_count += 1;

        log::info!(
            "{indent}  {target_name}: {:.1}ms (salsa memoized)",
            t_infer.as_secs_f64() * 1000.0,
        );
    }

    ImportResolution {
        types,
        errors,
        targets,
    }
}

/// Parallel import resolution path. Used when the number of imports exceeds
/// PARALLEL_THRESHOLD. Delegates to the two-phase parallel_imports module:
/// Phase 1 discovers the import graph, Phase 2 infers in parallel via rayon.
#[allow(clippy::too_many_arguments)]
fn resolve_imports_parallel(
    db: &dyn AstDb,
    file: NixFile,
    module: &Module,
    name_res: &NameResolution,
    work: &[(ImportKind, PathBuf)],
    cache: &mut HashMap<PathBuf, OutputTy>,
    aggregate_deadline: Instant,
    cancel_flag: Option<&Arc<AtomicBool>>,
    max_imports: Option<usize>,
) -> ImportResolution {
    use crate::parallel_imports::{discover_import_graph, infer_import_graph_parallel};
    use crate::salsa_imports::build_type_alias_registry;
    use std::sync::Arc;

    let file_path = file.path(db);

    let t0 = Instant::now();

    // Phase 1: Discover import graph (sequential, uses Salsa).
    let (graph, errors) = discover_import_graph(
        db,
        module,
        name_res,
        &file_path,
        max_imports,
        Some(aggregate_deadline),
        cancel_flag,
    );

    let t_discover = t0.elapsed();
    log::info!(
        "parallel import discovery: {} files in {:.1}ms",
        graph.len(),
        t_discover.as_secs_f64() * 1000.0,
    );

    // Phase 2: Infer in parallel via rayon.
    let aliases = match db.stub_config() {
        Some(config) => Arc::new(build_type_alias_registry(db, config)),
        None => Arc::new(crate::aliases::TypeAliasRegistry::default()),
    };

    let cancel_arc = cancel_flag.map(Arc::clone);
    let t0 = Instant::now();
    let inferred = infer_import_graph_parallel(&graph, aliases, 5, cancel_arc);
    let t_infer = t0.elapsed();
    log::info!(
        "parallel import inference: {} files in {:.1}ms",
        inferred.len(),
        t_infer.as_secs_f64() * 1000.0,
    );

    // Map inferred results back to the work list's ExprIds and build
    // navigation targets.
    let mut types = HashMap::new();
    let mut targets = HashMap::new();

    for (kind, target_path) in work {
        let target_path = target_path.canonicalize().unwrap_or(target_path.clone());
        let target_path = match resolve_directory_path(target_path.clone()) {
            Some(p) => p,
            None => continue,
        };

        // Record navigation targets.
        match kind {
            ImportKind::Import { apply_expr_id } => {
                if let Expr::Apply { fun, arg } = &module[*apply_expr_id] {
                    targets.insert(*fun, target_path.clone());
                    targets.insert(*arg, target_path.clone());
                }
                targets.insert(*apply_expr_id, target_path.clone());
            }
            ImportKind::CallPackage {
                outer_apply_id,
                inner_apply_id,
                path_literal_id,
            } => {
                targets.insert(*path_literal_id, target_path.clone());
                targets.insert(*outer_apply_id, target_path.clone());
                targets.insert(*inner_apply_id, target_path.clone());
            }
        }

        // Look up the inferred type.
        if let Some(root_ty) = inferred.get(&target_path) {
            cache.insert(target_path.clone(), root_ty.clone());
            match kind {
                ImportKind::Import { apply_expr_id } => {
                    types.insert(*apply_expr_id, root_ty.clone());
                }
                ImportKind::CallPackage {
                    outer_apply_id,
                    inner_apply_id,
                    ..
                } => {
                    types.insert(*inner_apply_id, root_ty.clone());
                    types.insert(*outer_apply_id, extract_return_type(root_ty));
                }
            }
        }
    }

    ImportResolution {
        types,
        errors,
        targets,
    }
}
