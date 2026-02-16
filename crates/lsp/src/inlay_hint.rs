// ==============================================================================
// textDocument/inlayHint — show inferred types inline
// ==============================================================================
//
// Displays the inferred type after name bindings and parameters, like:
//   let x :: int = 42 + 1; in x
// Skips trivial bindings where the type is obvious from the literal value
// (e.g. `let x = 42` — int is obvious).

use lang_ast::{BindingValue, Expr, ExprId, Literal, NameId, NameKind};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::*;

use crate::state::FileAnalysis;

pub fn inlay_hints(analysis: &FileAnalysis, range: Range, root: &rnix::Root) -> Vec<InlayHint> {
    let inference = match analysis.inference() {
        Some(inf) => inf,
        None => return Vec::new(),
    };

    let mut hints = Vec::new();

    for (name_id, name) in analysis.module.names() {
        // Skip inherit-style attrset keys where there's no binding value to
        // examine (the type comes from the inherited name, not this site).
        // All other name kinds — LetIn, Param, PatField, RecAttrset, and
        // PlainAttrset with a non-trivial value — are candidates for hints.

        // Get the name's source position.
        let ptr = match analysis.source_map.nodes_for_name(name_id).next() {
            Some(p) => p,
            None => continue,
        };
        let node = ptr.to_node(root.syntax());
        let name_range = analysis.line_index.range(node.text_range());

        // Filter to the requested range.
        if name_range.end.line < range.start.line || name_range.start.line > range.end.line {
            continue;
        }

        // Look up the inferred type.
        let ty = match inference.name_ty_map.get(name_id) {
            Some(t) => t,
            None => continue,
        };

        // For bindings (let, attrset fields), skip trivial types where the value
        // is a simple literal — the type is obvious from syntax. Also skip
        // inherit-style bindings (no value expression) since the type is shown
        // at the original definition.
        if matches!(
            name.kind,
            NameKind::LetIn | NameKind::RecAttrset | NameKind::PlainAttrset
        ) {
            match find_binding_expr(analysis, name_id) {
                Some(_) if is_trivial_binding(analysis, name_id) => continue,
                None => continue, // inherit — no value expression at this site
                _ => {}
            }
        }

        // Position the hint after the name.
        let position = name_range.end;

        hints.push(InlayHint {
            position,
            label: InlayHintLabel::String(format!(" :: {ty}")),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: None,
            padding_left: None,
            padding_right: None,
            data: None,
        });
    }

    hints
}

/// Check if a name's binding value is a trivial literal (int, float, string,
/// bool, path) whose type is obvious from the syntax.
fn is_trivial_binding(analysis: &FileAnalysis, name_id: NameId) -> bool {
    if let Some(expr_id) = find_binding_expr(analysis, name_id) {
        matches!(
            &analysis.module[expr_id],
            Expr::Literal(
                Literal::Integer(_) | Literal::Float(_) | Literal::String(_) | Literal::Path(_)
            )
        )
    } else {
        false
    }
}

/// Find the value ExprId for a name's binding. Searches LetIn and AttrSet
/// bindings in the module for the given name.
fn find_binding_expr(analysis: &FileAnalysis, target: NameId) -> Option<ExprId> {
    for (_, expr) in analysis.module.exprs() {
        let bindings = match expr {
            Expr::LetIn { bindings, .. } | Expr::AttrSet { bindings, .. } => bindings,
            _ => continue,
        };
        for &(name_id, ref value) in bindings.statics.iter() {
            if name_id == target {
                return match value {
                    BindingValue::Expr(e) => Some(*e),
                    _ => None,
                };
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::TestAnalysis;

    fn get_hints(src: &str) -> Vec<InlayHint> {
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();

        // Request hints for the full document.
        let full_range = Range::new(Position::new(0, 0), Position::new(u32::MAX, 0));
        inlay_hints(analysis, full_range, &t.root)
    }

    fn hint_labels(hints: &[InlayHint]) -> Vec<String> {
        hints
            .iter()
            .map(|h| match &h.label {
                InlayHintLabel::String(s) => s.clone(),
                InlayHintLabel::LabelParts(parts) => {
                    parts.iter().map(|p| p.value.as_str()).collect()
                }
            })
            .collect()
    }

    #[test]
    fn shows_hint_for_non_trivial_binding() {
        let src = "let x = 1 + 2; in x";
        let hints = get_hints(src);
        let labels = hint_labels(&hints);
        // x's type should appear (the binding is not a trivial literal).
        assert!(
            labels.iter().any(|l| l.contains("::")),
            "should show type hint for computed binding: {labels:?}"
        );
    }

    #[test]
    fn skips_trivial_integer_literal() {
        let src = "let x = 42; in x";
        let hints = get_hints(src);
        // x = 42 is a trivial literal — no hint expected for x.
        let x_hints: Vec<_> = hints
            .iter()
            .filter(|h| match &h.label {
                InlayHintLabel::String(s) => s.contains("int"),
                _ => false,
            })
            .collect();
        assert!(
            x_hints.is_empty(),
            "should skip trivial int literal: {x_hints:?}"
        );
    }

    #[test]
    fn shows_hint_for_lambda_param() {
        let src = "x: x + 1";
        let hints = get_hints(src);
        // Lambda param `x` should always get a hint (type not obvious from syntax).
        assert!(!hints.is_empty(), "should show hint for lambda param");
    }

    #[test]
    fn shows_hints_for_pattern_fields() {
        let src = "{ name, src, ... }: name";
        let hints = get_hints(src);
        // Both `name` and `src` should get hints.
        assert!(
            hints.len() >= 2,
            "should show hints for pattern fields, got {}: {:?}",
            hints.len(),
            hint_labels(&hints)
        );
    }

    #[test]
    fn shows_hints_for_plain_attrset_fields() {
        // Top-level attrsets (like simple.nix) have PlainAttrset names.
        // Non-trivial bindings should still get hints.
        let src = "{ add = a: b: a + b; addOne = add 1; x = 42; }";
        let hints = get_hints(src);
        let labels = hint_labels(&hints);
        // `add` (lambda) and `addOne` (non-trivial) should get hints.
        // `x = 42` is trivial and should be skipped.
        // `a` and `b` are params and should get hints.
        assert!(
            labels.len() >= 2,
            "should show hints for non-trivial attrset fields: {labels:?}"
        );
    }

    #[test]
    fn skips_inherit_in_attrset() {
        // `inherit` attrset fields have no value expression at this site,
        // so they shouldn't get hints (the type is on the original binding).
        let src = "let f = x: x; in { inherit f; }";
        let hints = get_hints(src);
        let labels = hint_labels(&hints);
        // `f` in the let should get a hint, but `f` in `inherit f` should not.
        let f_hints: Vec<_> = labels.iter().filter(|l| l.contains("->")).collect();
        assert_eq!(
            f_hints.len(),
            1,
            "should show hint only for the let binding, not the inherit: {labels:?}"
        );
    }

    #[test]
    fn empty_range_returns_empty() {
        let src = "let x = 1 + 2; y = 3 + 4; in x + y";
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();

        // Request a range that contains no names (past end of file).
        let range = Range::new(Position::new(100, 0), Position::new(101, 0));
        let hints = inlay_hints(analysis, range, &t.root);
        assert!(hints.is_empty());
    }
}
