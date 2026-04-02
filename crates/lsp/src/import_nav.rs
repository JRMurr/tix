// ==============================================================================
// Cross-file import navigation primitives
// ==============================================================================
//
// Shared logic for following import chains transitively (goto-def) and
// finding field references across importing files (find-all-references).

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstDb, Expr, ExprId, Literal, Module, NameId};
use lang_check::imports::resolve_import_types;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Range, Url};

use crate::state::{AnalysisState, SyntaxData};

/// Maximum depth for transitive import resolution to prevent infinite loops.
const MAX_DEPTH: usize = 8;

// ==============================================================================
// Transitive field resolution (for goto-def)
// ==============================================================================

/// Resolve a field name through barrel re-exports transitively.
///
/// Starting from `target_path`, finds the name matching `field_name` and checks
/// if it's bound to an import. If so, follows through to the import target and
/// repeats until either:
/// - The name is not an import (actual definition) → returns its Location
/// - The target file has no matching name → returns Location at file start
/// - Depth limit reached → returns Location of last found name
pub fn resolve_field_transitively(
    state: &AnalysisState,
    target_path: &Path,
    field_name: &str,
) -> Option<Location> {
    let mut current_path = if target_path.is_dir() {
        target_path.join("default.nix")
    } else {
        target_path.to_path_buf()
    };

    for depth in 0..MAX_DEPTH {
        log::debug!(
            "resolve_field_transitively: depth={depth}, path={}, field={field_name}",
            current_path.display()
        );
        let target_file = state.db.load_file(&current_path)?;
        let (target_module, target_source_map) =
            lang_ast::module_and_source_maps(&state.db, target_file);
        let target_contents = target_file.contents(&state.db);
        let target_root = rnix::Root::parse(target_contents).tree();

        // Find a name in the target module matching the field name.
        let found = target_module
            .names()
            .find(|(_, name)| name.text == field_name);

        let name_res = lang_ast::name_resolution(&state.db, target_file);
        let indices = lang_ast::module_indices(&state.db, target_file);
        let base_dir = current_path.parent().unwrap_or(Path::new("/"));

        let (target_name_id, _) = match found {
            Some(hit) => hit,
            None => {
                // No matching name in this file. Check if the file's return value
                // is a pass-through reference to an import (e.g. `let res = import ./x.nix; in res`).
                // If so, follow through to the imported file and look for the field there.
                let import_resolution =
                    resolve_import_types(&target_module, &name_res, base_dir, |_| None, None);
                if let Some(next_path) = resolve_return_value_import(
                    &target_module,
                    &name_res,
                    &indices,
                    &import_resolution.targets,
                ) {
                    log::debug!(
                        "resolve_field_transitively: file returns import pass-through -> {}",
                        next_path.display()
                    );
                    current_path = if next_path.is_dir() {
                        next_path.join("default.nix")
                    } else {
                        next_path
                    };
                    continue;
                }

                // Truly no match — jump to file start.
                let target_uri = Url::from_file_path(&current_path).ok()?;
                return Some(Location::new(
                    target_uri,
                    Range::new(Position::new(0, 0), Position::new(0, 0)),
                ));
            }
        };

        // Cheap import resolution — only resolves paths, no type inference.
        let import_resolution =
            resolve_import_types(&target_module, &name_res, base_dir, |_| None, None);

        // Check if the binding expression for this name is an import.
        if let Some(&binding_expr) = indices.binding_expr.get(&target_name_id) {
            if let Some(next_path) =
                chase_import_target(&target_module, &import_resolution.targets, binding_expr)
            {
                log::debug!(
                    "resolve_field_transitively: field {field_name} is re-export -> {}",
                    next_path.display()
                );
                // This name is a re-export — follow through to the import target.
                current_path = if next_path.is_dir() {
                    next_path.join("default.nix")
                } else {
                    next_path.clone()
                };
                continue;
            }
        }

        // Not an import — this is the actual definition. Return its location.
        let target_ptr = target_source_map.nodes_for_name(target_name_id).next()?;
        let target_node = target_ptr.to_node(target_root.syntax());
        let target_line_index = crate::convert::LineIndex::new(target_contents);
        let target_range = target_line_index.range(target_node.text_range());
        let target_uri = Url::from_file_path(&current_path).ok()?;
        return Some(Location::new(target_uri, target_range));
    }

    // Depth limit reached — jump to last file.
    let target_uri = Url::from_file_path(&current_path).ok()?;
    Some(Location::new(
        target_uri,
        Range::new(Position::new(0, 0), Position::new(0, 0)),
    ))
}

// ==============================================================================
// Cross-file field references (for find-all-references)
// ==============================================================================

/// Find references to `field_name` across files that import `origin_path`.
///
/// Scans all analyzed files that import `origin_path` for Select expressions
/// like `lib.field_name` where `lib` is bound to the import.
///
/// Only searches files with existing snapshots (open/analyzed files). Files
/// that haven't been analyzed yet are skipped.
pub fn find_cross_file_field_references(
    state: &AnalysisState,
    snapshots: &dashmap::DashMap<PathBuf, crate::state::FileSnapshot>,
    origin_path: &Path,
    field_name: &str,
) -> Vec<Location> {
    let dependents = state.coordinator.get_dependents(origin_path);
    let mut locations = Vec::new();

    for importer_path in &dependents {
        if let Some(snap) = snapshots.get(importer_path) {
            let refs = scan_file_for_field_references(
                &snap.syntax,
                origin_path,
                field_name,
                importer_path,
            );
            locations.extend(refs);
        }
    }

    locations
}

/// Scan a single file's syntax data for Select expressions accessing `field_name`
/// on a binding that imports `origin_path`.
fn scan_file_for_field_references(
    syntax: &SyntaxData,
    origin_path: &Path,
    field_name: &str,
    file_path: &Path,
) -> Vec<Location> {
    let uri = match Url::from_file_path(file_path) {
        Ok(u) => u,
        Err(_) => return vec![],
    };

    // Find all NameIds that are bound to imports of origin_path.
    let import_names: HashSet<NameId> = syntax
        .name_to_import
        .iter()
        .filter(|(_, path)| paths_equal(path, origin_path))
        .map(|(&name_id, _)| name_id)
        .collect();

    if import_names.is_empty() {
        return vec![];
    }

    let root = syntax.parsed.tree();
    let mut locations = Vec::new();

    for (_, expr) in syntax.module.exprs() {
        if let Expr::Select { set, attrpath, .. } = expr {
            // Check if the base (`set`) resolves to one of the import names.
            if let Expr::Reference(_) = &syntax.module[*set] {
                if let Some(ResolveResult::Definition(name_id)) = syntax.name_res.get(*set) {
                    if import_names.contains(name_id) {
                        // Check the first attrpath element matches field_name.
                        if let Some(&attr_expr_id) = attrpath.first() {
                            if let Expr::Literal(Literal::String(s)) = &syntax.module[attr_expr_id]
                            {
                                if s == field_name {
                                    if let Some(ptr) = syntax.source_map.node_for_expr(attr_expr_id)
                                    {
                                        let node = ptr.to_node(root.syntax());
                                        let range = syntax.line_index.range(node.text_range());
                                        locations.push(Location::new(uri.clone(), range));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    locations
}

/// Check if a file's return value is a reference to an import (pass-through pattern).
///
/// Unwraps through Lambda and LetIn to find the innermost body expression.
/// If it's a Reference that resolves to a name bound to an import, returns the
/// import target path. This handles the pattern:
/// ```nix
/// { pkgs }: let res = import ./real.nix { inherit pkgs; }; in res
/// ```
fn resolve_return_value_import(
    module: &Module,
    name_res: &lang_ast::NameResolution,
    indices: &lang_ast::ModuleIndices,
    import_targets: &std::collections::HashMap<ExprId, PathBuf>,
) -> Option<PathBuf> {
    // Unwrap through Lambda/LetIn to find the innermost return expression.
    let mut expr_id = module.entry_expr;
    for _ in 0..20 {
        match &module[expr_id] {
            Expr::Lambda { body, .. } => expr_id = *body,
            Expr::LetIn { body, .. } => expr_id = *body,
            _ => break,
        }
    }

    // Check if the return expression is a reference.
    if let Expr::Reference(_) = &module[expr_id] {
        if let Some(ResolveResult::Definition(name_id)) = name_res.get(expr_id) {
            // Check if the referenced name is bound to an import.
            if let Some(&binding_expr) = indices.binding_expr.get(name_id) {
                return chase_import_target(module, import_targets, binding_expr);
            }
        }
    }

    // Also handle direct import as return value: `import ./foo.nix`
    chase_import_target(module, import_targets, expr_id)
}

/// Chase through Apply chains to find an import target path.
///
/// `import ./foo.nix { args }` desugars to `Apply(Apply(import, ./foo.nix), { args })`.
/// The inner Apply is in `import_targets`, but the outer one isn't. This walks the
/// `fun` chain until it finds a match.
fn chase_import_target(
    module: &Module,
    import_targets: &std::collections::HashMap<ExprId, PathBuf>,
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

/// Compare two paths for equality, using canonicalization when possible.
fn paths_equal(a: &Path, b: &Path) -> bool {
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(ca), Ok(cb)) => ca == cb,
        _ => a == b,
    }
}
