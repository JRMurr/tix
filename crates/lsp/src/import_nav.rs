// ==============================================================================
// Cross-file import navigation primitives
// ==============================================================================
//
// Shared logic for following import chains transitively (goto-def) and
// finding field references across importing files (find-all-references).

use rustc_hash::FxHashSet as HashSet;
use std::path::{Path, PathBuf};

use lang_ast::nameres::ResolveResult;
use lang_ast::{Expr, ExprId, Literal, Module, NameId};
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
    _state: &AnalysisState,
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
        let target_contents = std::fs::read_to_string(&current_path).ok()?;
        let r = lang_ast::run_syntax_pipeline_for_file(&current_path, &target_contents);
        let target_root = rnix::Root::parse(&target_contents).tree();

        // Find a name in the target module matching the field name.
        let found = r.module.names().find(|(_, name)| name.text == field_name);

        let base_dir = current_path.parent().unwrap_or(Path::new("/"));

        let (target_name_id, _) = match found {
            Some(hit) => hit,
            None => {
                // No matching name in this file. Check if the file's return value
                // is a pass-through reference to an import (e.g. `let res = import ./x.nix; in res`).
                // If so, follow through to the imported file and look for the field there.
                let import_resolution =
                    resolve_import_types(&r.module, &r.name_res, base_dir, |_| None, None);
                if let Some(next_path) = resolve_return_value_import(
                    &r.module,
                    &r.name_res,
                    &r.module_indices,
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
            resolve_import_types(&r.module, &r.name_res, base_dir, |_| None, None);

        // Check if the binding expression for this name is an import.
        if let Some(&binding_expr) = r.module_indices.binding_expr.get(&target_name_id) {
            if let Some(next_path) =
                chase_import_target(&r.module, &import_resolution.targets, binding_expr)
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
        let target_ptr = r.source_map.nodes_for_name(target_name_id).next()?;
        let target_node = target_ptr.to_node(target_root.syntax());
        let target_line_index = crate::convert::LineIndex::new(target_contents.as_str());
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
/// When a dependent is a pass-through barrel (imports origin_path and returns
/// the result directly without accessing the field), recursively searches
/// the barrel's own dependents.
///
/// Only searches files with existing snapshots (open/analyzed files). Files
/// that haven't been analyzed yet are skipped.
pub fn find_cross_file_field_references(
    state: &AnalysisState,
    snapshots: &dashmap::DashMap<PathBuf, crate::state::FileSnapshot>,
    origin_path: &Path,
    field_name: &str,
) -> Vec<Location> {
    let mut locations = Vec::new();
    let mut visited = HashSet::default();
    find_cross_file_field_references_inner(
        state,
        snapshots,
        origin_path,
        field_name,
        &mut locations,
        &mut visited,
    );
    locations
}

fn find_cross_file_field_references_inner(
    state: &AnalysisState,
    snapshots: &dashmap::DashMap<PathBuf, crate::state::FileSnapshot>,
    origin_path: &Path,
    field_name: &str,
    locations: &mut Vec<Location>,
    visited: &mut HashSet<PathBuf>,
) {
    if !visited.insert(origin_path.to_path_buf()) {
        return;
    }

    let dependents = state.coordinator.get_dependents(origin_path);

    for importer_path in &dependents {
        if let Some(snap) = snapshots.get(importer_path) {
            let refs = scan_file_for_field_references(
                &snap.syntax,
                origin_path,
                field_name,
                importer_path,
            );

            if refs.is_empty() {
                // No direct field references in this file. Check if it's a
                // pass-through barrel that re-exports origin_path's value.
                // If so, files importing THIS file might access the field.
                if is_passthrough_of(&snap.syntax, origin_path) {
                    find_cross_file_field_references_inner(
                        state,
                        snapshots,
                        importer_path,
                        field_name,
                        locations,
                        visited,
                    );
                }
            } else {
                locations.extend(refs);
            }
        }
    }
}

/// Check if a file is a pass-through barrel for the given origin path.
/// A pass-through file imports origin_path and returns the result directly.
fn is_passthrough_of(syntax: &SyntaxData, origin_path: &Path) -> bool {
    // Check if any name in this file is bound to an import of origin_path.
    // name_to_import paths are canonicalized at build time, so canonicalize
    // the origin once and compare directly.
    let origin_canon = origin_path.canonicalize();
    let origin: &Path = origin_canon.as_deref().unwrap_or(origin_path);
    let import_names: Vec<_> = syntax
        .name_to_import
        .iter()
        .filter(|(_, path)| path.as_path() == origin)
        .map(|(&name_id, _)| name_id)
        .collect();

    if import_names.is_empty() {
        return false;
    }

    // Check if the file's return value is a reference to one of those import names.
    let mut expr_id = syntax.module.entry_expr;
    for _ in 0..20 {
        match &syntax.module[expr_id] {
            Expr::Lambda { body, .. } => expr_id = *body,
            Expr::LetIn { body, .. } => expr_id = *body,
            _ => break,
        }
    }

    if let Expr::Reference(_) = &syntax.module[expr_id] {
        if let Some(ResolveResult::Definition(name_id)) = syntax.name_res.get(expr_id) {
            return import_names.contains(name_id);
        }
    }

    false
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
    // name_to_import paths are canonicalized at build time — see above.
    let origin_canon = origin_path.canonicalize();
    let origin: &Path = origin_canon.as_deref().unwrap_or(origin_path);
    let import_names: HashSet<NameId> = syntax
        .name_to_import
        .iter()
        .filter(|(_, path)| path.as_path() == origin)
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
    import_targets: &rustc_hash::FxHashMap<ExprId, PathBuf>,
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
    import_targets: &rustc_hash::FxHashMap<ExprId, PathBuf>,
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
