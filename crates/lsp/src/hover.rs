// ==============================================================================
// textDocument/hover — show inferred type on hover
// ==============================================================================
//
// Converts the cursor position to a byte offset, finds the smallest syntax
// node at that offset, maps it to an ExprId or NameId via the source map,
// then looks up the inferred type.

use lang_ast::AstPtr;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Hover, HoverContents, MarkedString, Position, Range};

use crate::state::FileAnalysis;

/// Try to produce hover information for the given cursor position.
pub fn hover(analysis: &FileAnalysis, pos: Position, root: &rnix::Root) -> Option<Hover> {
    let inference = analysis.inference()?;
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    // Walk up from the token to find the smallest node that has a source map entry.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Check for a name at this node first (shows the binding's type).
        if let Some(name_id) = analysis.source_map.name_for_node(ptr) {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                let name_text = &analysis.module[name_id].text;
                let range = analysis.line_index.range(node.text_range());
                return Some(make_hover(format!("{name_text} :: {ty}"), range));
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            if let Some(ty) = inference.expr_ty_map.get(expr_id) {
                let range = analysis.line_index.range(node.text_range());
                return Some(make_hover(format!("{ty}"), range));
            }
        }

        node = node.parent()?;
    }
}

fn make_hover(text: String, range: Range) -> Hover {
    Hover {
        contents: HoverContents::Scalar(MarkedString::LanguageString(
            tower_lsp::lsp_types::LanguageString {
                language: "tix".to_string(),
                value: text,
            },
        )),
        range: Some(range),
    }
}
