// ==============================================================================
// textDocument/references — find all references to a name
// ==============================================================================
//
// Also provides `name_at_position`, a shared helper used by document highlight
// and rename to resolve the NameId under the cursor.

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr, NameId};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::state::FileSnapshot;

/// Find the NameId under the cursor. Works on both definition sites (where a
/// name is bound) and reference sites (where a name is used).
pub fn name_at_position(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
) -> Option<NameId> {
    let offset = analysis.syntax.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

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
                if let Some(ResolveResult::Definition(name_id)) = analysis.syntax.name_res.get(expr_id) {
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
