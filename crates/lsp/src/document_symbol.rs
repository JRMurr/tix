// ==============================================================================
// textDocument/documentSymbol — outline of names in the file
// ==============================================================================
//
// Walks the lowered Module AST to produce a hierarchical list of symbols
// (let bindings, attrset fields, function definitions) for the editor's
// outline view and breadcrumbs.

use lang_ast::{BindingValue, Expr, ExprId, NameId};
use tower_lsp::lsp_types::{DocumentSymbol, Range, SymbolKind};

use crate::state::FileAnalysis;

#[allow(deprecated)] // DocumentSymbol.deprecated is deprecated but required by the struct
pub fn document_symbols(analysis: &FileAnalysis, root: &rnix::Root) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();
    collect_symbols(analysis, root, analysis.module.entry_expr, &mut symbols);
    symbols
}

/// Recursively collect symbols from an expression.
fn collect_symbols(
    analysis: &FileAnalysis,
    root: &rnix::Root,
    expr_id: ExprId,
    out: &mut Vec<DocumentSymbol>,
) {
    match &analysis.module[expr_id] {
        Expr::LetIn { bindings, body } => {
            collect_binding_symbols(analysis, root, &bindings.statics, false, out);
            collect_symbols(analysis, root, *body, out);
        }
        Expr::AttrSet { bindings, .. } => {
            collect_binding_symbols(analysis, root, &bindings.statics, true, out);
        }
        // For other expression types, just recurse into children to find
        // nested let-in or attrset expressions.
        other => {
            other.walk_child_exprs(|child| {
                collect_symbols(analysis, root, child, out);
            });
        }
    }
}

/// Emit a symbol for each static binding in a let-in or attrset.
#[allow(deprecated)]
fn collect_binding_symbols(
    analysis: &FileAnalysis,
    root: &rnix::Root,
    statics: &[(NameId, BindingValue)],
    is_attrset: bool,
    out: &mut Vec<DocumentSymbol>,
) {
    use rowan::ast::AstNode;

    for &(name_id, ref binding_value) in statics {
        let name = &analysis.module[name_id];
        let name_text = name.text.to_string();

        // Determine symbol kind from the binding value expression.
        let (kind, value_expr_id) = match binding_value {
            BindingValue::Expr(expr_id) => {
                let kind = match &analysis.module[*expr_id] {
                    Expr::Lambda { .. } => SymbolKind::FUNCTION,
                    _ if is_attrset => SymbolKind::PROPERTY,
                    _ => SymbolKind::VARIABLE,
                };
                (kind, Some(*expr_id))
            }
            BindingValue::Inherit(_) => {
                let kind = if is_attrset {
                    SymbolKind::PROPERTY
                } else {
                    SymbolKind::VARIABLE
                };
                (kind, None)
            }
            // InheritFrom is a synthetic entry; skip it.
            BindingValue::InheritFrom(_) => continue,
        };

        // Get the name's source range for selection_range.
        let selection_range = match analysis.source_map.nodes_for_name(name_id).next() {
            Some(ptr) => {
                let node = ptr.to_node(root.syntax());
                analysis.line_index.range(node.text_range())
            }
            None => continue,
        };

        // For the full symbol range, combine the name range with the value
        // expression's range (if available).
        let range = match value_expr_id.and_then(|eid| analysis.source_map.node_for_expr(eid)) {
            Some(val_ptr) => {
                let val_node = val_ptr.to_node(root.syntax());
                let val_range = analysis.line_index.range(val_node.text_range());
                // Combine: earliest start to latest end.
                Range::new(
                    std::cmp::min_by(selection_range.start, val_range.start, |a, b| {
                        (a.line, a.character).cmp(&(b.line, b.character))
                    }),
                    std::cmp::max_by(selection_range.end, val_range.end, |a, b| {
                        (a.line, a.character).cmp(&(b.line, b.character))
                    }),
                )
            }
            None => selection_range,
        };

        // Recurse into nested attrset values for children.
        let children = match value_expr_id {
            Some(eid) if matches!(&analysis.module[eid], Expr::AttrSet { .. }) => {
                let mut child_symbols = Vec::new();
                collect_symbols(analysis, root, eid, &mut child_symbols);
                if child_symbols.is_empty() {
                    None
                } else {
                    Some(child_symbols)
                }
            }
            _ => None,
        };

        out.push(DocumentSymbol {
            name: name_text,
            detail: None,
            kind,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::TestAnalysis;

    fn get_symbols(src: &str) -> Vec<DocumentSymbol> {
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();
        document_symbols(analysis, &t.root)
    }

    fn names(symbols: &[DocumentSymbol]) -> Vec<&str> {
        let mut n: Vec<&str> = symbols.iter().map(|s| s.name.as_str()).collect();
        n.sort();
        n
    }

    #[test]
    fn let_bindings_produce_variable_symbols() {
        let symbols = get_symbols(r#"let x = 1; y = "hello"; in x"#);
        assert_eq!(symbols.len(), 2);
        assert_eq!(names(&symbols), vec!["x", "y"]);
        assert!(symbols.iter().all(|s| s.kind == SymbolKind::VARIABLE));
    }

    #[test]
    fn attrset_fields_produce_property_symbols() {
        let symbols = get_symbols("{ a = 1; b = 2; }");
        assert_eq!(symbols.len(), 2);
        assert_eq!(names(&symbols), vec!["a", "b"]);
        assert!(symbols.iter().all(|s| s.kind == SymbolKind::PROPERTY));
    }

    #[test]
    fn nested_attrset_has_children() {
        let symbols = get_symbols("{ a = 1; b = { c = 2; }; }");
        assert_eq!(symbols.len(), 2);
        assert_eq!(names(&symbols), vec!["a", "b"]);
        let b = symbols.iter().find(|s| s.name == "b").unwrap();
        let children = b.children.as_ref().expect("b should have children");
        assert_eq!(children.len(), 1);
        assert_eq!(children[0].name, "c");
        assert_eq!(children[0].kind, SymbolKind::PROPERTY);
    }

    #[test]
    fn lambda_binding_is_function_kind() {
        let symbols = get_symbols("let f = x: x; in f");
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "f");
        assert_eq!(symbols[0].kind, SymbolKind::FUNCTION);
    }

    #[test]
    fn plain_literal_produces_no_symbols() {
        let symbols = get_symbols("42");
        assert!(symbols.is_empty());
    }
}
