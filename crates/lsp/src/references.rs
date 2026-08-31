// ==============================================================================
// textDocument/references — find all references to a name
// ==============================================================================
//
// Also provides `name_at_position`, a shared helper used by document highlight
// and rename to resolve the NameId under the cursor.

use std::path::PathBuf;

use dashmap::DashMap;
use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr, Literal, NameId};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::state::FileSnapshot;

/// Find the NameId under the cursor. Works on both definition sites (where a
/// name is bound) and reference sites (where a name is used).
///
/// When the cursor is at a token boundary (e.g. end of an identifier), we try
/// right-biased first, then fall back to left-biased. This handles the common
/// case where editors send the cursor position at the end of the word.
pub fn name_at_position(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
) -> Option<NameId> {
    let offset = analysis.syntax.line_index.offset(pos);
    let token_at = root.syntax().token_at_offset(rowan::TextSize::from(offset));

    // Try right-biased first (handles cursor at start/middle of token),
    // then left-biased (handles cursor at end of identifier).
    let right = token_at.clone().right_biased();
    let left = token_at.left_biased();

    for token in right.into_iter().chain(left) {
        if let Some(name_id) = resolve_token_to_name(analysis, &token) {
            return Some(name_id);
        }
    }

    None
}

/// Walk up from a token to find a NameId (definition or reference site).
fn resolve_token_to_name(
    analysis: &FileSnapshot,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<NameId> {
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Definition site: the cursor is on a name node (let binding, param, etc.).
        if let Some(name_id) = analysis.syntax.source_map.name_for_node(ptr) {
            return Some(name_id);
        }

        // Reference site: the cursor is on a variable reference that resolves
        // to a definition.
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            if matches!(&analysis.syntax.module[expr_id], Expr::Reference(_)) {
                if let Some(ResolveResult::Definition(name_id)) =
                    analysis.syntax.name_res.get(expr_id)
                {
                    return Some(*name_id);
                }
            }
            // Found an expression but it's not a resolvable reference — stop.
            return None;
        }

        node = node.parent()?;
    }
}

/// Find all reference locations for the name under the cursor.
pub fn find_references(
    analysis: &FileSnapshot,
    pos: Position,
    uri: &Url,
    root: &rnix::Root,
    include_declaration: bool,
) -> Vec<Location> {
    let target = match name_at_position(analysis, pos, root) {
        Some(n) => n,
        None => return Vec::new(),
    };

    let mut locations = Vec::new();

    // Use the inverted index to find all references to the target name.
    for &expr_id in analysis.syntax.name_res.refs_to(target) {
        if let Some(ptr) = analysis.syntax.source_map.node_for_expr(expr_id) {
            let node = ptr.to_node(root.syntax());
            let range = analysis.syntax.line_index.range(node.text_range());
            locations.push(Location::new(uri.clone(), range));
        }
    }

    // Add the declaration site itself.
    if include_declaration {
        if let Some(ptr) = analysis.syntax.source_map.nodes_for_name(target).next() {
            let node = ptr.to_node(root.syntax());
            let range = analysis.syntax.line_index.range(node.text_range());
            locations.push(Location::new(uri.clone(), range));
        }
    }

    locations
}

/// Find all references to a name, including cross-file references via imports.
///
/// Extends `find_references` with cross-file search:
/// - If the cursor is on a name definition or reference, finds `x.name` usages
///   in files that import this file.
/// - If the cursor is on a Select field literal (e.g. `helper` in `lib.helper`),
///   resolves to the target file's definition and finds all references from there.
pub fn find_references_cross_file(
    coordinator: &lang_check::coordinator::InferenceCoordinator,
    snapshots: &DashMap<PathBuf, FileSnapshot>,
    analysis: &FileSnapshot,
    pos: Position,
    uri: &Url,
    root: &rnix::Root,
    include_declaration: bool,
) -> Vec<Location> {
    // Try the normal name-based path first.
    if let Some(target_name_id) = name_at_position(analysis, pos, root) {
        let mut locations = find_references(analysis, pos, uri, root, include_declaration);

        let file_path = match uri.to_file_path() {
            Ok(p) => p,
            Err(_) => return locations,
        };
        let name_text = &analysis.syntax.module[target_name_id].text;

        let cross_file = crate::import_nav::find_cross_file_field_references(
            coordinator,
            snapshots,
            &file_path,
            name_text,
        );
        locations.extend(cross_file);

        return locations;
    }

    // No NameId under cursor — check if it's a Select field literal.
    // e.g. cursor on `helper` in `lib.helper` where lib = import ./lib.nix.
    if let Some((target_file_path, field_name)) =
        resolve_select_field_at_position(analysis, pos, root)
    {
        return references_for_field_in_file(
            coordinator,
            snapshots,
            &target_file_path,
            &field_name,
            include_declaration,
        );
    }

    Vec::new()
}

/// When the cursor is on a Select field literal (e.g. `helper` in `lib.helper`),
/// resolve it to the target file path and field name. Uses the same import
/// resolution as goto-def.
fn resolve_select_field_at_position(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
) -> Option<(PathBuf, String)> {
    let token = crate::convert::token_at_pos(
        &analysis.syntax.line_index,
        root,
        pos,
        crate::convert::Bias::Right,
    )?;

    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            // Check if this is a string literal inside a Select (field name).
            if let Expr::Literal(Literal::String(field_name)) = &analysis.syntax.module[expr_id] {
                // Walk up to find the enclosing Select.
                let select_node = node.ancestors().find_map(rnix::ast::Select::cast)?;
                let base_syntax = select_node.expr()?;
                let base_ptr = AstPtr::new(base_syntax.syntax());
                let base_expr_id = analysis.syntax.source_map.expr_for_node(base_ptr)?;

                // Resolve the base to an import target path.
                let target_path =
                    if let Some(path) = analysis.syntax.import_targets.get(&base_expr_id) {
                        path.clone()
                    } else if let Expr::Reference(_) = &analysis.syntax.module[base_expr_id] {
                        let res = analysis.syntax.name_res.get(base_expr_id)?;
                        if let ResolveResult::Definition(name_id) = res {
                            analysis.syntax.name_to_import.get(name_id)?.clone()
                        } else {
                            return None;
                        }
                    } else {
                        return None;
                    };

                return Some((target_path, field_name.to_string()));
            }
            return None;
        }
        node = node.parent()?;
    }
}

/// Find all references to a field defined in a specific file.
/// Returns the declaration in the target file + cross-file usages.
fn references_for_field_in_file(
    coordinator: &lang_check::coordinator::InferenceCoordinator,
    snapshots: &DashMap<PathBuf, FileSnapshot>,
    target_file_path: &std::path::Path,
    field_name: &str,
    include_declaration: bool,
) -> Vec<Location> {
    let mut locations = Vec::new();

    // Resolve transitively through barrels to find the actual definition file.
    // This reuses the same logic as goto-def.
    let resolved = crate::import_nav::resolve_field_transitively(target_file_path, field_name);

    // Add the declaration site if requested.
    if include_declaration {
        if let Some(loc) = &resolved {
            locations.push(loc.clone());
        }
    }

    // Determine which file actually defines this field (after barrel resolution).
    let def_file_path = resolved
        .as_ref()
        .and_then(|loc| loc.uri.to_file_path().ok())
        .unwrap_or_else(|| target_file_path.to_path_buf());

    // Find cross-file references from the definition file.
    let cross_file = crate::import_nav::find_cross_file_field_references(
        coordinator,
        snapshots,
        &def_file_path,
        field_name,
    );
    locations.extend(cross_file);

    locations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;

    fn refs_at_marker(src: &str, marker: u32, include_declaration: bool) -> Vec<Location> {
        let markers = parse_markers(src);
        let offset = markers[&marker];
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();
        let uri = t.uri();
        let pos = analysis.syntax.line_index.position(offset);
        find_references(&analysis, pos, &uri, &t.root, include_declaration)
    }

    #[test]
    fn references_for_let_binding() {
        let src = indoc! {"
            let x = 1; in x + x
            #   ^1         ^2
        "};

        // From the definition site.
        let refs = refs_at_marker(src, 1, false);
        assert_eq!(refs.len(), 2, "should find 2 references to x");

        let refs_with_decl = refs_at_marker(src, 1, true);
        assert_eq!(
            refs_with_decl.len(),
            3,
            "should find 2 refs + 1 declaration"
        );
    }

    #[test]
    fn references_from_usage_site() {
        let src = indoc! {"
            let x = 1; in x + x
            #             ^1
        "};

        let refs = refs_at_marker(src, 1, true);
        assert_eq!(refs.len(), 3, "should find 2 refs + 1 declaration");
    }

    #[test]
    fn no_references_for_unused_binding() {
        let src = indoc! {"
            let x = 1; y = 2; in y
            #   ^1
        "};

        let refs = refs_at_marker(src, 1, false);
        assert_eq!(refs.len(), 0, "x has no references");
    }

    /// Regression: cursor at the end of an identifier (right after the last
    /// char) should still resolve to that name. VS Code often sends the cursor
    /// position at the end of the word when the user presses F2.
    #[test]
    fn name_at_end_of_identifier() {
        let src = "let foo = 1; in foo";
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();

        // Position cursor right after `foo` in the definition (byte offset 7,
        // which is the space after `foo`). This is what VS Code sends when the
        // cursor is at the end of the word.
        let pos = analysis.syntax.line_index.position(7); // "let foo " -> after 'o'
        let result = name_at_position(&analysis, pos, &t.root);
        assert!(
            result.is_some(),
            "cursor at end of identifier `foo` (offset 7, pos {:?}) should resolve to a name",
            pos,
        );
    }

    #[test]
    fn with_expr_returns_empty() {
        let src = indoc! {"
            with { foo = 1; }; foo
            #                  ^1
        "};

        let refs = refs_at_marker(src, 1, true);
        assert!(refs.is_empty(), "with-resolved names have no NameId");
    }
}
