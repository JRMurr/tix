// ==============================================================================
// textDocument/signatureHelp — show parameter info during function calls
// ==============================================================================
//
// When the cursor is inside a function application (e.g. `f arg1 arg2`), this
// handler looks up the function's inferred type and presents its parameter
// signature. For curried functions (`a -> b -> c`), we determine which
// parameter position the cursor is at by counting how deeply nested we are
// in the Apply chain. For pattern parameters (`{ name, src, ... }: T`), we
// show the expected fields.

use lang_ast::AstPtr;
use lang_ty::OutputTy;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{
    Documentation, MarkupContent, MarkupKind, ParameterInformation, ParameterLabel, Position,
    SignatureHelp, SignatureInformation,
};

use crate::state::FileAnalysis;

/// Entry point: try to produce signature help for the given cursor position.
///
/// Walks up from the cursor token looking for enclosing Apply nodes. When
/// found, resolves the outermost function in the Apply chain and retrieves
/// its inferred type, then builds a signature with the active parameter
/// highlighted based on which argument subtree the cursor falls in.
pub fn signature_help(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
) -> Option<SignatureHelp> {
    let inference = analysis.inference()?;
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .left_biased()?;

    let node = token.parent()?;

    // Find the outermost Apply node that the cursor is part of.
    // In Nix, `f a b c` parses as Apply(Apply(Apply(f, a), b), c).
    //
    // Strategy: walk up ancestors collecting all Apply nodes. Then from the
    // outermost Apply, walk the function-side Apply chain to find the root
    // function and all argument positions. Finally, determine which argument
    // the cursor is in.
    let outermost_apply = find_outermost_apply(&node)?;

    // Flatten the Apply chain: collect all (function, argument) pairs from
    // the outermost Apply downward. This gives us the arguments in order.
    let chain = flatten_apply_chain(&outermost_apply);
    if chain.is_empty() {
        return None;
    }

    // The root function is the lambda (function) side of the innermost Apply.
    let root_fun_node = &chain[0].0;
    let root_fun_ptr = AstPtr::new(root_fun_node.syntax());
    let root_fun_expr_id = analysis.source_map.expr_for_node(root_fun_ptr)?;

    // Look up the function's inferred type.
    let fun_ty = inference.expr_ty_map.get(root_fun_expr_id)?;

    // Determine the active parameter by checking which argument range contains
    // the cursor.
    let cursor_offset = rowan::TextSize::from(offset);
    let total_params = chain.len();
    let mut active_param: u32 = (total_params - 1) as u32; // default to last

    for (i, (_fun, arg)) in chain.iter().enumerate() {
        if arg.syntax().text_range().contains_inclusive(cursor_offset) {
            active_param = i as u32;
            break;
        }
    }

    build_signature_help(fun_ty, total_params, active_param)
}

/// Walk up from a syntax node through ancestors, collecting the outermost
/// Apply node that forms a contiguous application chain.
///
/// For `f a b c` (parsed as `Apply(Apply(Apply(f, a), b), c)`), starting
/// from any node within this expression, this returns the outermost Apply.
fn find_outermost_apply(node: &rnix::SyntaxNode) -> Option<rnix::ast::Apply> {
    let mut result: Option<rnix::ast::Apply> = None;

    for ancestor in node.ancestors() {
        if let Some(apply) = rnix::ast::Apply::cast(ancestor) {
            result = Some(apply);
        } else if result.is_some() {
            // We hit a non-Apply ancestor, so the chain is done.
            break;
        }
    }

    result
}

/// Flatten an Apply chain into a list of (function, argument) pairs in
/// application order (first param first).
///
/// For `Apply(Apply(Apply(f, a), b), c)`:
/// - outermost.lambda() = `Apply(Apply(f, a), b)`, outermost.argument() = `c`
/// - next.lambda() = `Apply(f, a)`, next.argument() = `b`
/// - innermost.lambda() = `f`, innermost.argument() = `a`
///
/// Returns: `[(f, a), (Apply(f,a), b), (Apply(Apply(f,a),b), c)]`
/// i.e. the root function `f` is at index 0, and the arguments are in call order.
fn flatten_apply_chain(outermost: &rnix::ast::Apply) -> Vec<(rnix::ast::Expr, rnix::ast::Expr)> {
    let mut stack = Vec::new();
    let mut current = outermost.clone();

    loop {
        let arg = match current.argument() {
            Some(a) => a,
            None => break,
        };
        let fun = match current.lambda() {
            Some(f) => f,
            None => break,
        };

        stack.push((fun.clone(), arg));

        // If the function side is also an Apply, descend into it.
        match fun {
            rnix::ast::Expr::Apply(inner) => {
                current = inner;
            }
            _ => break,
        }
    }

    // Reverse so the first parameter is at index 0.
    stack.reverse();
    stack
}

/// Build `SignatureHelp` from a function type, the number of parameters
/// being applied, and the active parameter index.
fn build_signature_help(
    fun_ty: &OutputTy,
    num_params: usize,
    active_param: u32,
) -> Option<SignatureHelp> {
    // Collect the parameter types from the function type by peeling off
    // Lambda layers.
    let param_types = collect_param_types(fun_ty, num_params);
    if param_types.is_empty() {
        return None;
    }

    // Build the signature label and parameter labels.
    let (label, param_labels, param_docs) = format_signature(fun_ty, &param_types);

    let parameters: Vec<ParameterInformation> = param_labels
        .into_iter()
        .zip(param_docs)
        .map(|(label_str, doc)| ParameterInformation {
            label: ParameterLabel::Simple(label_str),
            documentation: doc.map(|d| {
                Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: d,
                })
            }),
        })
        .collect();

    let signature = SignatureInformation {
        label,
        documentation: None,
        parameters: Some(parameters),
        active_parameter: Some(active_param),
    };

    Some(SignatureHelp {
        signatures: vec![signature],
        active_signature: Some(0),
        active_parameter: Some(active_param),
    })
}

/// Peel off Lambda layers from a function type to extract parameter types.
/// Stops after `max_params` or when the type is no longer a Lambda.
fn collect_param_types(ty: &OutputTy, max_params: usize) -> Vec<OutputTy> {
    let mut params = Vec::new();
    let mut current = ty.clone();

    for _ in 0..max_params {
        match unwrap_named(&current) {
            OutputTy::Lambda { param, body } => {
                params.push((*param.0).clone());
                current = (*body.0).clone();
            }
            _ => break,
        }
    }

    params
}

/// Unwrap Named wrappers to get at the structural type.
fn unwrap_named(ty: &OutputTy) -> OutputTy {
    match ty {
        OutputTy::Named(_, inner) => unwrap_named(&inner.0),
        other => other.clone(),
    }
}

/// Format the signature label and parameter labels for display.
///
/// For a function type `a -> b -> c`, the label is `a -> b -> c` and the
/// parameter labels are `["a", "b"]`.
///
/// For a pattern parameter (`{ name: string, src: path, ... } -> T`),
/// the parameter label shows the field names.
fn format_signature(
    fun_ty: &OutputTy,
    param_types: &[OutputTy],
) -> (String, Vec<String>, Vec<Option<String>>) {
    let mut label_parts = Vec::new();
    let mut param_labels = Vec::new();
    let mut param_docs = Vec::new();

    for param_ty in param_types {
        let param_str = format_param_type(param_ty);
        label_parts.push(param_str.clone());
        param_labels.push(param_str);
        param_docs.push(format_param_doc(param_ty));
    }

    // Add the return type.
    let return_ty = peel_lambdas(fun_ty, param_types.len());
    label_parts.push(format!("{return_ty}"));

    let label = label_parts.join(" -> ");
    (label, param_labels, param_docs)
}

/// Format a single parameter type for the signature label.
///
/// For attrset types (pattern parameters), shows a condensed field list.
/// For other types, uses the standard display.
fn format_param_type(ty: &OutputTy) -> String {
    match unwrap_named_ref(ty) {
        OutputTy::AttrSet(ref attr) => {
            // Show field names with types for pattern parameters.
            let mut parts = Vec::new();
            for (name, field_ty) in &attr.fields {
                parts.push(format!("{name}: {field_ty}"));
            }
            if attr.open {
                parts.push("...".to_string());
            }
            format!("{{ {} }}", parts.join(", "))
        }
        // For lambda params, parenthesize to avoid ambiguity in the signature.
        OutputTy::Lambda { .. } => format!("({ty})"),
        // For union/intersection params, parenthesize.
        OutputTy::Union(_) | OutputTy::Intersection(_) => format!("({ty})"),
        _ => format!("{ty}"),
    }
}

/// Get documentation for a parameter type (e.g. listing pattern fields).
fn format_param_doc(ty: &OutputTy) -> Option<String> {
    match unwrap_named_ref(ty) {
        OutputTy::AttrSet(ref attr) if !attr.fields.is_empty() => {
            let mut lines = vec!["**Fields:**".to_string()];
            for (name, field_ty) in &attr.fields {
                let opt = if attr.optional_fields.contains(name) {
                    " (optional)"
                } else {
                    ""
                };
                lines.push(format!("- `{name}`: `{field_ty}`{opt}"));
            }
            if attr.open {
                lines.push("- `...` (accepts additional fields)".to_string());
            }
            Some(lines.join("\n"))
        }
        _ => None,
    }
}

/// Unwrap Named wrappers, returning a reference to the structural type.
fn unwrap_named_ref(ty: &OutputTy) -> &OutputTy {
    match ty {
        OutputTy::Named(_, inner) => unwrap_named_ref(&inner.0),
        other => other,
    }
}

/// Peel off `n` Lambda layers from a type and return the resulting return type.
fn peel_lambdas(ty: &OutputTy, n: usize) -> OutputTy {
    let mut current = ty.clone();
    for _ in 0..n {
        match unwrap_named(&current) {
            OutputTy::Lambda { body, .. } => {
                current = (*body.0).clone();
            }
            _ => break,
        }
    }
    current
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;

    /// Helper: get signature help at a byte offset.
    fn sig_help_at(t: &TestAnalysis, offset: u32) -> Option<SignatureHelp> {
        let analysis = t.analysis();
        let pos = analysis.line_index.position(offset);
        signature_help(analysis, pos, &t.root)
    }

    /// Extract the signature label from a SignatureHelp result.
    fn sig_label(help: &SignatureHelp) -> &str {
        &help.signatures[0].label
    }

    /// Extract the active parameter index from a SignatureHelp result.
    fn active_param(help: &SignatureHelp) -> u32 {
        help.signatures[0]
            .active_parameter
            .or(help.active_parameter)
            .unwrap_or(0)
    }

    /// Extract parameter labels from a SignatureHelp result.
    fn param_labels(help: &SignatureHelp) -> Vec<&str> {
        help.signatures[0]
            .parameters
            .as_ref()
            .map(|params| {
                params
                    .iter()
                    .map(|p| match &p.label {
                        ParameterLabel::Simple(s) => s.as_str(),
                        ParameterLabel::LabelOffsets(_) => "<offsets>",
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    // ------------------------------------------------------------------
    // Basic function application
    // ------------------------------------------------------------------

    #[test]
    fn signature_help_simple_function() {
        // `f` is `int -> int`, cursor on the argument `1`.
        let src = indoc! {"
            let f = x: x + 1;
            in f 1
            #    ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        assert_eq!(active_param(&help), 0, "cursor should be on first param");
        let params = param_labels(&help);
        assert!(!params.is_empty(), "should have at least one parameter");
    }

    #[test]
    fn signature_help_curried_function() {
        // `add` is `int -> int -> int`, cursor on the second argument.
        let src = indoc! {"
            let add = x: y: x + y;
            in add 1 2
            #        ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        assert_eq!(active_param(&help), 1, "cursor should be on second param");
        let params = param_labels(&help);
        assert!(
            params.len() >= 2,
            "curried function should show at least 2 params, got: {params:?}"
        );
    }

    #[test]
    fn signature_help_first_param_of_curried() {
        // Cursor on the first argument of a curried function.
        let src = indoc! {"
            let add = x: y: x + y;
            in add 1 2
            #      ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        assert_eq!(active_param(&help), 0, "cursor should be on first param");
    }

    #[test]
    fn signature_help_pattern_param() {
        // Function with a pattern parameter: `{ name, src, ... }: ...`.
        // The signature should show the expected fields.
        let src = indoc! {r#"
            let f = { name, src, ... }: name + src;
            in f { name = "hello"; src = "world"; }
            #    ^1
        "#};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        let label = sig_label(&help);
        // The param type should mention the fields (name, src).
        assert!(
            label.contains("name") || label.contains("src"),
            "pattern param signature should mention field names, got: {label}"
        );
    }

    #[test]
    fn signature_help_no_help_outside_apply() {
        // Cursor on a plain variable, not inside an application.
        let src = indoc! {"
            let x = 1;
            in x
            #  ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]);
        assert!(
            help.is_none(),
            "should not get signature help outside function application"
        );
    }

    #[test]
    fn signature_help_shows_return_type() {
        // The signature label should include the return type after the arrow(s).
        let src = indoc! {"
            let f = x: x + 1;
            in f 1
            #    ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        let label = sig_label(&help);
        // The label should contain `->` separating param from return type.
        assert!(
            label.contains("->"),
            "signature should include arrow notation, got: {label}"
        );
    }

    #[test]
    fn signature_help_three_params() {
        // Three-parameter curried function: `a -> b -> c -> d`.
        let src = indoc! {"
            let f = a: b: c: a + b + c;
            in f 1 2 3
            #         ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        assert_eq!(active_param(&help), 2, "cursor should be on third param");
        let params = param_labels(&help);
        assert!(
            params.len() >= 3,
            "should have at least 3 params, got: {params:?}"
        );
    }

    #[test]
    fn signature_help_pattern_param_doc() {
        // Pattern param should generate documentation listing the fields.
        let src = indoc! {r#"
            let f = { name, src, ... }: name + src;
            in f { name = "hello"; src = "world"; }
            #    ^1
        "#};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]).expect("should get signature help");

        // Check that at least one parameter has documentation.
        let has_doc = help.signatures[0]
            .parameters
            .as_ref()
            .map(|params| params.iter().any(|p| p.documentation.is_some()))
            .unwrap_or(false);

        assert!(
            has_doc,
            "pattern parameter should have documentation listing fields"
        );
    }

    #[test]
    fn signature_help_on_space_after_function_name() {
        // Cursor on the space between function name and first argument.
        // `left_biased` lands on the space token which is inside the Apply
        // node, so we should still get signature help.
        let src = indoc! {"
            let f = x: x + 1;
            in f 1
            #   ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let help = sig_help_at(&t, markers[&1]);
        assert!(
            help.is_some(),
            "cursor on space before first arg should give signature help"
        );
    }
}
