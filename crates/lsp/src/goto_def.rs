// ==============================================================================
// textDocument/definition — jump to where a name is defined
// ==============================================================================
//
// For a Reference expression under the cursor, looks up name resolution to
// find the definition NameId, then maps that back to a source location via
// the source map.

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::state::FileAnalysis;

/// Try to find the definition location for the symbol at the given cursor position.
pub fn goto_definition(
    analysis: &FileAnalysis,
    pos: Position,
    uri: &Url,
    root: &rnix::Root,
) -> Option<Location> {
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    // Walk up from the token to find a node that is a Reference expression.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            // Only handle Reference expressions — other expressions don't
            // have a meaningful "definition" to jump to.
            if matches!(&analysis.module[expr_id], Expr::Reference(_)) {
                if let Some(res) = analysis.name_res.get(expr_id) {
                    match res {
                        ResolveResult::Definition(name_id) => {
                            // Find the source location of the definition.
                            if let Some(def_ptr) = analysis.source_map.nodes_for_name(*name_id).next() {
                                let def_node = def_ptr.to_node(root.syntax());
                                let range = analysis.line_index.range(def_node.text_range());
                                return Some(Location::new(uri.clone(), range));
                            }
                        }
                        // Builtins and `with` expressions don't have a source
                        // definition we can jump to within this file.
                        ResolveResult::Builtin(_) | ResolveResult::WithExprs(_) => {}
                    }
                }
            }
            // Found an expression node but it's not a reference — stop walking.
            return None;
        }

        node = node.parent()?;
    }
}
