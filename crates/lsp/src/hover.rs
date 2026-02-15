// ==============================================================================
// textDocument/hover — show inferred type on hover
// ==============================================================================
//
// Converts the cursor position to a byte offset, finds the smallest syntax
// node at that offset, maps it to an ExprId or NameId via the source map,
// then looks up the inferred type. If stub docs are available for the hovered
// name or field, they're appended below the type.

use lang_ast::{AstPtr, Expr};
use lang_check::aliases::DocIndex;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Hover, HoverContents, MarkedString, Position, Range};

use crate::state::FileAnalysis;

/// Try to produce hover information for the given cursor position.
pub fn hover(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
    docs: &DocIndex,
) -> Option<Hover> {
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

                // Look up doc comment for this name from stubs.
                let doc = docs.decl_doc(name_text.as_str());
                return Some(make_hover(
                    format!("{name_text} :: {ty}"),
                    doc.map(|d| d.as_str()),
                    range,
                ));
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            if let Some(ty) = inference.expr_ty_map.get(expr_id) {
                let range = analysis.line_index.range(node.text_range());

                // For Select expressions, try to find field-level docs by
                // walking the Select chain to build a field path and finding
                // the base name's type alias.
                let doc = try_select_field_doc(analysis, expr_id, docs);
                return Some(make_hover(format!("{ty}"), doc.as_deref(), range));
            }
        }

        node = node.parent()?;
    }
}

/// Walk a Select expression chain to extract the field path and look up
/// field-level docs from the DocIndex.
///
/// For `config.services.openssh.enable`, the AST is nested Selects:
///   Select(Select(Select(config, services), openssh), enable)
///
/// We walk inward to find the base name (config), then look up the
/// type alias associated with it (e.g. NixosConfig), and query the
/// DocIndex with the field path (services.openssh.enable).
fn try_select_field_doc(
    analysis: &FileAnalysis,
    expr_id: lang_ast::ExprId,
    docs: &DocIndex,
) -> Option<String> {
    use lang_ast::Literal;

    let module = &analysis.module;

    // Build the field path by walking Select chains outward.
    // The current expr_id is the outermost Select.
    let mut path = Vec::new();
    let mut current = expr_id;

    loop {
        match &module[current] {
            Expr::Select { set, attrpath, .. } => {
                // Attrpath segments are ExprIds — we need to get their string names.
                // They're typically Literal(String(...)) expressions.
                for &attr_expr in attrpath.iter().rev() {
                    if let Expr::Literal(Literal::String(s)) = &module[attr_expr] {
                        path.push(s.clone());
                    }
                }
                current = *set;
            }
            Expr::Reference(ref_name) => {
                // Found the base reference. Look up what type alias it might be.
                // Expr::Reference stores the identifier text as SmolStr.

                // Try to find the inferred type for the expression to extract
                // the alias name. If the expression type display starts with an
                // uppercase letter, it's likely a Named alias.
                let inference = analysis.inference()?;
                if let Some(ty) = inference.expr_ty_map.get(current) {
                    let ty_str = ty.to_string();
                    if ty_str
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_uppercase())
                    {
                        let alias_name = ty_str.split_whitespace().next().unwrap_or(&ty_str);
                        path.reverse();
                        return docs.field_doc(alias_name, &path).map(|d| d.to_string());
                    }
                }

                // Fallback: try capitalizing the base name as an alias name.
                let capitalized = capitalize_first(ref_name);
                path.reverse();
                return docs.field_doc(&capitalized, &path).map(|d| d.to_string());
            }
            _ => return None,
        }
    }
}

/// Capitalize the first character of a string.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().chain(chars).collect(),
    }
}

fn make_hover(type_text: String, doc: Option<&str>, range: Range) -> Hover {
    let mut parts = vec![MarkedString::LanguageString(
        tower_lsp::lsp_types::LanguageString {
            language: "tix".to_string(),
            value: type_text,
        },
    )];

    if let Some(doc) = doc {
        parts.push(MarkedString::String(doc.to_string()));
    }

    Hover {
        contents: HoverContents::Array(parts),
        range: Some(range),
    }
}
