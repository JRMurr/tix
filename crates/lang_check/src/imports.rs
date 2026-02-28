// ==============================================================================
// Import Resolution
// ==============================================================================
//
// Scans the AST for `import <literal-path>` and `callPackage <literal-path> {}`
// patterns, then resolves types from ephemeral stubs (inferred types of
// open/analyzed files). Files without stubs default to ⊤ (the generic
// `import :: a -> b` builtin type).
//
// For `callPackage`, the target file's root type is a function (the package
// derivation). Since callPackage applies the dependency-injection argument, we
// peel one Lambda layer to get the return type.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use lang_ast::nameres::ResolveResult;
use lang_ast::{Expr, ExprId, Literal, Module, NameResolution};
use lang_ty::OutputTy;

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
                // Directory exists but has no default.nix.
                continue;
            }
        };

        // Record navigation targets (Apply, fun/Reference, arg/Literal).
        if let Expr::Apply { fun, arg } = &module[apply_expr_id] {
            targets.insert(*fun, target_path.clone());
            targets.insert(*arg, target_path.clone());
        }
        targets.insert(apply_expr_id, target_path.clone());

        // Look up ephemeral stub first — if found, use it regardless of
        // whether the file exists on disk (the stub proves we've seen it).
        if let Some(stub_ty) = ephemeral_stubs.get(&target_path) {
            types.insert(apply_expr_id, stub_ty.clone());
            continue;
        }

        // No stub available. If the file doesn't exist on disk either,
        // report an error. Otherwise fall through to the generic
        // `import :: a -> b` builtin type.
        if !target_path.exists() {
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: apply_expr_id,
            });
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
            None => continue,
        };

        // Record navigation targets.
        targets.insert(path_literal_id, target_path.clone());
        targets.insert(outer_apply_id, target_path.clone());
        targets.insert(inner_apply_id, target_path.clone());

        // Look up ephemeral stub first.
        if let Some(stub_ty) = ephemeral_stubs.get(&target_path) {
            types.insert(inner_apply_id, stub_ty.clone());
            types.insert(outer_apply_id, extract_return_type(stub_ty));
            continue;
        }

        // No stub — report FileNotFound if the file doesn't exist on disk.
        if !target_path.exists() {
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: outer_apply_id,
            });
        }
    }

    ImportResolution {
        types,
        errors,
        targets,
    }
}

// Old resolve_imports() and resolve_imports_parallel() have been deleted.
// Import types now come from ephemeral stubs (see resolve_import_types_from_stubs).
