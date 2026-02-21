// ==============================================================================
// Multi-File Import Resolution
// ==============================================================================
//
// Before inference begins for a file, we scan its AST for `import <literal-path>`
// patterns, recursively infer each target file, and build a pre-computed
// `ExprId -> OutputTy` map. This map is passed into CheckCtx so that Apply
// expressions matching resolved imports use the imported file's root type
// instead of the unconstrained `a -> b` from the builtin `import` signature.
//
// Type isolation: each imported file is inferred in its own CheckCtx with its
// own TypeStorage. The result is canonicalized to immutable OutputTy values.
// When the importing file interns the OutputTy, it creates fresh TyIds in its
// own storage — no cross-file mutation is possible.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstDb, Expr, ExprId, Literal, Module, NameResolution, NixFile};
use lang_ty::OutputTy;

use crate::aliases::TypeAliasRegistry;

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

        let resolved = base_dir.join(path_str);
        imports.push((expr_id, resolved));
    }

    imports
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

/// Recursively resolve all literal imports in a file.
///
/// For each `import <literal-path>` found in the AST:
/// - If the target is already being resolved (in `in_progress`), record a cyclic
///   import error.
/// - If the target was already resolved (in `cache`), reuse the cached type.
/// - Otherwise, load and infer the target file recursively, then cache the result.
///
/// The `cache` prevents re-inferring files in diamond import patterns (A imports
/// B and C, both of which import D — D is inferred only once).
pub fn resolve_imports(
    db: &dyn AstDb,
    file: NixFile,
    module: &Module,
    name_res: &NameResolution,
    aliases: &TypeAliasRegistry,
    in_progress: &mut HashSet<PathBuf>,
    cache: &mut HashMap<PathBuf, OutputTy>,
) -> ImportResolution {
    // Determine the base directory for resolving relative import paths.
    let file_path = file.path(db);
    let base_dir = file_path.parent().unwrap_or(Path::new("/"));

    let literal_imports = scan_literal_imports(module, name_res, base_dir);

    let mut types = HashMap::new();
    let mut errors = Vec::new();
    let mut targets = HashMap::new();

    for (apply_expr_id, target_path) in literal_imports {
        // Canonicalize the path so cycle detection and caching work correctly
        // even with symlinks or `..` components. Fall back to the raw path
        // when canonicalization fails (e.g. in-memory test databases where
        // the path doesn't exist on disk).
        let target_path = target_path.canonicalize().unwrap_or(target_path);

        // Record navigation targets for the LSP before any cycle/cache/load
        // checks, so even failed imports get jump-to-definition support.
        if let Expr::Apply { fun, arg } = &module[apply_expr_id] {
            targets.insert(*fun, target_path.clone());
            targets.insert(*arg, target_path.clone());
        }
        targets.insert(apply_expr_id, target_path.clone());

        // Check for cycles.
        if in_progress.contains(&target_path) {
            errors.push(ImportError {
                kind: ImportErrorKind::CyclicImport(target_path),
                at_expr: apply_expr_id,
            });
            continue;
        }

        // Check cache.
        if let Some(cached_ty) = cache.get(&target_path) {
            types.insert(apply_expr_id, cached_ty.clone());
            continue;
        }

        // Load and infer the target file.
        let Some(target_file) = db.load_file(&target_path) else {
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: apply_expr_id,
            });
            continue;
        };

        let target_module = lang_ast::module(db, target_file);
        let target_name_res = lang_ast::name_resolution(db, target_file);
        let target_grouped = lang_ast::group_def(db, target_file);

        // Mark as in-progress before recursing to detect cycles.
        in_progress.insert(target_path.clone());

        // Recursively resolve imports in the target file.
        let target_imports = resolve_imports(
            db,
            target_file,
            &target_module,
            &target_name_res,
            aliases,
            in_progress,
            cache,
        );

        in_progress.remove(&target_path);

        // Collect import errors from the target file (propagate diagnostics).
        errors.extend(target_imports.errors);

        // Infer the target file with its own resolved imports.
        // Imported files don't get context args — those only apply to the
        // root file being type-checked (or via per-lambda doc comments).
        let target_indices = lang_ast::module_indices(db, target_file);
        let check = crate::CheckCtx::new(
            &target_module,
            &target_name_res,
            &target_indices.binding_expr,
            aliases.clone(),
            target_imports.types,
            std::collections::HashMap::new(),
        );

        match check.infer_prog(target_grouped) {
            Ok(result) => {
                let root_ty = result
                    .expr_ty_map
                    .get(target_module.entry_expr)
                    .cloned()
                    .unwrap_or(OutputTy::TyVar(0));

                cache.insert(target_path, root_ty.clone());
                types.insert(apply_expr_id, root_ty);
            }
            Err(err) => {
                errors.push(ImportError {
                    kind: ImportErrorKind::InferenceError(target_path, err),
                    at_expr: apply_expr_id,
                });
            }
        }
    }

    ImportResolution {
        types,
        errors,
        targets,
    }
}
