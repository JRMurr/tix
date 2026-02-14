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

pub fn inlay_hints(
    analysis: &FileAnalysis,
    range: Range,
    root: &rnix::Root,
) -> Vec<InlayHint> {
    let inference = match analysis.inference() {
        Some(inf) => inf,
        None => return Vec::new(),
    };

    let mut hints = Vec::new();

    for (name_id, name) in analysis.module.names() {
        // Only show hints for definitions, not plain attrset keys.
        match name.kind {
            NameKind::LetIn | NameKind::Param | NameKind::PatField | NameKind::RecAttrset => {}
            NameKind::PlainAttrset => continue,
        }

        // Get the name's source position.
        let ptr = match analysis.source_map.nodes_for_name(name_id).next() {
            Some(p) => p,
            None => continue,
        };
        let node = ptr.to_node(root.syntax());
        let name_range = analysis.line_index.range(node.text_range());

        // Filter to the requested range.
        if name_range.end.line < range.start.line
            || name_range.start.line > range.end.line
        {
            continue;
        }

        // Look up the inferred type.
        let ty = match inference.name_ty_map.get(&name_id) {
            Some(t) => t,
            None => continue,
        };

        // For LetIn and RecAttrset bindings, skip trivial types where the value
        // is a simple literal — the type is obvious from syntax.
        if matches!(name.kind, NameKind::LetIn | NameKind::RecAttrset)
            && is_trivial_binding(analysis, name_id)
        {
            continue;
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
                Literal::Integer(_)
                    | Literal::Float(_)
                    | Literal::String(_)
                    | Literal::Path(_)
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
    use crate::state::AnalysisState;
    use crate::test_util::temp_path;
    use lang_check::aliases::TypeAliasRegistry;

    fn get_hints(src: &str) -> Vec<InlayHint> {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        // Request hints for the full document.
        let full_range = Range::new(Position::new(0, 0), Position::new(u32::MAX, 0));
        inlay_hints(analysis, full_range, &root)
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
        assert!(
            !hints.is_empty(),
            "should show hint for lambda param"
        );
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
    fn empty_range_returns_empty() {
        let src = "let x = 1 + 2; y = 3 + 4; in x + y";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        // Request a range that contains no names (past end of file).
        let range = Range::new(Position::new(100, 0), Position::new(101, 0));
        let hints = inlay_hints(analysis, range, &root);
        assert!(hints.is_empty());
    }
}
