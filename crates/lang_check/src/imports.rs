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
use std::path::{Component, Path, PathBuf};

use lang_ast::nameres::ResolveResult;
use lang_ast::{Expr, ExprId, Literal, Module, NameResolution};
use lang_ty::{OutputTy, OwnedTy};

// ==============================================================================
// Import Scanning
// ==============================================================================

/// Result of scanning literal imports: resolved paths and angle bracket imports.
pub struct ScannedImports {
    /// Successfully resolved `(apply_expr_id, resolved_path)` pairs.
    pub resolved: Vec<(ExprId, PathBuf)>,
    /// Angle bracket imports that could not be resolved.
    pub angle_bracket: Vec<ImportError>,
}

/// Scan a module's AST for `import <literal-path>` patterns.
///
/// Walks all expressions looking for Apply nodes where:
/// - `fun` is a Reference("import") that resolves to Builtin("import")
/// - `arg` is a Literal(Path(..))
///
/// Returns resolved `(apply_expr_id, resolved_path)` pairs and angle bracket
/// import errors. Non-literal import args (interpolations, variables, etc.)
/// are silently skipped — they remain as unconstrained type variables via the
/// normal `import :: a -> b` synthesis.
pub fn scan_literal_imports(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
) -> ScannedImports {
    let mut resolved = Vec::new();
    let mut angle_bracket = Vec::new();

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

        // Angle bracket search paths (e.g. `<nixpkgs>`) require NIX_PATH
        // resolution which we don't implement yet. Record them as diagnostics
        // so users know why the type is unconstrained.
        // TODO: resolve via NIX_PATH
        if path_str.starts_with('<') {
            angle_bracket.push(ImportError {
                kind: ImportErrorKind::AngleBracketImport(path_str.clone()),
                at_expr: expr_id,
            });
            continue;
        }

        let path = base_dir.join(path_str);
        resolved.push((expr_id, path));
    }

    ScannedImports {
        resolved,
        angle_bracket,
    }
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
pub(crate) fn extract_return_type(owned: &OwnedTy) -> OwnedTy {
    match owned.arena.get(owned.root) {
        OutputTy::Lambda { body, .. } => OwnedTy::new(owned.arena.clone(), *body),
        OutputTy::Named(_, inner) => {
            let inner_owned = OwnedTy::new(owned.arena.clone(), *inner);
            extract_return_type(&inner_owned)
        }
        _ => owned.clone(),
    }
}

// ==============================================================================
// Bulk Import Path Scanning (for dependency graph construction)
// ==============================================================================

/// Normalize path components (`.`, `..`) without any syscalls.
///
/// Safe when `base_dir` is already canonical — the joined path won't contain
/// symlinks that would make textual `..` resolution incorrect.
fn normalize_path(path: &Path) -> PathBuf {
    let mut out = Vec::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            c => out.push(c),
        }
    }
    out.iter().collect()
}

/// Scan a module for all import paths without resolving types.
///
/// Combines `scan_literal_imports` and `scan_callpackage_imports`, normalizes
/// paths, applies directory → `default.nix` resolution, and deduplicates.
/// Returns only normalized paths — no ExprIds, no types. Used by `tix check`
/// to build the file-level dependency graph before inference begins.
///
/// When `base_dir` is canonical, the returned paths are equivalent to
/// `canonicalize` results (no symlinks within the Nix store tree).
pub fn scan_all_import_paths(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
) -> Vec<PathBuf> {
    let literal = scan_literal_imports(module, name_res, base_dir);
    let callpackage = scan_callpackage_imports(module, base_dir);

    let mut seen = HashSet::new();
    let mut result = Vec::new();

    let all_paths = literal
        .resolved
        .iter()
        .map(|(_, p)| p.clone())
        .chain(callpackage.iter().map(|(_, _, _, p)| p.clone()));

    for path in all_paths {
        // Cheap textual normalization instead of canonicalize() syscall.
        // Safe because base_dir is already canonical (no symlinks to resolve).
        let normalized = normalize_path(&path);

        // Apply directory → default.nix resolution.
        let resolved = match resolve_directory_path(normalized) {
            Some(p) => p,
            None => continue, // Directory with no default.nix.
        };

        if seen.insert(resolved.clone()) {
            result.push(resolved);
        }
    }

    result
}

/// Resolve a path that may point to a directory, applying Nix's convention
/// of loading `default.nix` from directories.
///
/// Returns `None` if the path is a directory with no `default.nix`.
pub(crate) fn resolve_directory_path(path: PathBuf) -> Option<PathBuf> {
    if path.is_dir() {
        let default = path.join("default.nix");
        if default.is_file() {
            Some(normalize_path(&default))
        } else {
            None
        }
    } else {
        Some(path)
    }
}

// ==============================================================================
// Import Errors
// ==============================================================================

#[derive(Debug, Clone)]
pub enum ImportErrorKind {
    FileNotFound(PathBuf),
    /// An angle bracket import like `<nixpkgs>` that can't be resolved.
    AngleBracketImport(String),
    /// File exists but has no ephemeral stub (hasn't been analyzed).
    NoStubAvailable(PathBuf),
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
    pub types: HashMap<ExprId, OwnedTy>,
    /// Errors encountered during import resolution.
    pub errors: Vec<ImportError>,
    /// Maps ExprIds of import sub-expressions (Apply, Reference, Literal)
    /// to the resolved target path. Used by the LSP for jump-to-definition
    /// on `import ./foo.nix` expressions.
    pub targets: HashMap<ExprId, PathBuf>,
    /// Canonical import paths discovered during scanning. Populated from the
    /// scan results that `resolve_import_types` already computes, so callers
    /// don't need to re-scan to get the dependency list.
    pub resolved_paths: Vec<PathBuf>,
}

// ==============================================================================
// Import Type Resolution
// ==============================================================================

/// Resolve import types using a caller-provided lookup function.
///
/// For each scanned import target path:
/// 1. Records navigation targets (for goto-def) regardless of type availability
/// 2. Calls `lookup(canonicalized_path)` to get the imported file's root type
/// 3. Falls through to ⊤ (no entry in result map → builtin `import :: a -> b`)
///
/// The `lookup` closure abstracts over the type source — it can read from an
/// `ephemeral_stubs` HashMap, an `InferenceCoordinator` cache, or anything else.
pub fn resolve_import_types<F>(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
    lookup: F,
) -> ImportResolution
where
    F: Fn(&Path) -> Option<OwnedTy>,
{
    let scanned = scan_literal_imports(module, name_res, base_dir);
    let callpackage_imports = scan_callpackage_imports(module, base_dir);

    // Track which paths are already handled by regular imports so we don't
    // double-resolve files that appear in both `import ./x` and `callPackage ./x`.
    let import_paths: HashSet<PathBuf> = scanned
        .resolved
        .iter()
        .filter_map(|(_, p)| p.canonicalize().ok())
        .collect();

    // Pre-collect canonical import paths from both scan results before the
    // for loops consume the vectors. This populates resolved_paths so callers
    // (e.g. compute_file) don't need to re-scan.
    let resolved_paths: Vec<PathBuf> = scanned
        .resolved
        .iter()
        .map(|(_, p)| p.canonicalize().unwrap_or_else(|_| p.clone()))
        .chain(
            callpackage_imports
                .iter()
                .map(|(_, _, _, p)| p.canonicalize().unwrap_or_else(|_| p.clone())),
        )
        .collect();

    let mut types = HashMap::new();
    let mut errors: Vec<ImportError> = scanned.angle_bracket;
    let mut targets = HashMap::new();

    // ---- Literal imports ----
    for (apply_expr_id, target_path) in scanned.resolved {
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

        // Look up type via the provided lookup function.
        if let Some(stub_ty) = lookup(&target_path) {
            types.insert(apply_expr_id, stub_ty);
            continue;
        }

        // No type available. If the file doesn't exist on disk either,
        // report FileNotFound. If it exists but hasn't been analyzed,
        // report ImportUnresolved as a hint.
        if !target_path.exists() {
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: apply_expr_id,
            });
        } else {
            errors.push(ImportError {
                kind: ImportErrorKind::NoStubAvailable(target_path),
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

        // Look up type via the provided lookup function.
        if let Some(stub_ty) = lookup(&target_path) {
            types.insert(inner_apply_id, stub_ty.clone());
            types.insert(outer_apply_id, extract_return_type(&stub_ty));
            continue;
        }

        // No type — report FileNotFound or ImportUnresolved.
        if !target_path.exists() {
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(target_path),
                at_expr: outer_apply_id,
            });
        } else {
            errors.push(ImportError {
                kind: ImportErrorKind::NoStubAvailable(target_path),
                at_expr: outer_apply_id,
            });
        }
    }

    ImportResolution {
        types,
        errors,
        targets,
        resolved_paths,
    }
}

/// Resolve import types from a pre-populated stubs HashMap.
///
/// Thin wrapper around `resolve_import_types` for backward compatibility with
/// code that has a `HashMap<PathBuf, OutputTy>` of ephemeral stubs.
pub fn resolve_import_types_from_stubs(
    module: &Module,
    name_res: &NameResolution,
    base_dir: &Path,
    ephemeral_stubs: &HashMap<PathBuf, OwnedTy>,
) -> ImportResolution {
    resolve_import_types(module, name_res, base_dir, |p| {
        ephemeral_stubs.get(p).cloned()
    })
}

/// Convert import resolution errors into `TixDiagnostic`s for rendering in
/// CLI or LSP. Each `ImportError` becomes a warning-level diagnostic attached
/// to the expression where the import occurs.
pub fn import_errors_to_diagnostics(
    errors: &[ImportError],
) -> Vec<crate::diagnostic::TixDiagnostic> {
    errors
        .iter()
        .map(|err| {
            let kind = match &err.kind {
                ImportErrorKind::FileNotFound(path) => {
                    crate::diagnostic::TixDiagnosticKind::ImportNotFound {
                        path: path.display().to_string(),
                    }
                }
                ImportErrorKind::AngleBracketImport(path) => {
                    crate::diagnostic::TixDiagnosticKind::AngleBracketImport { path: path.clone() }
                }
                ImportErrorKind::NoStubAvailable(path) => {
                    crate::diagnostic::TixDiagnosticKind::ImportUnresolved {
                        path: path.display().to_string(),
                    }
                }
            };
            crate::diagnostic::TixDiagnostic {
                at_expr: err.at_expr,
                kind,
            }
        })
        .collect()
}
