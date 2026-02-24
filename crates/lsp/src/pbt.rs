// ==============================================================================
// Property-based tests for LSP crash freedom
// ==============================================================================
//
// Generates structurally diverse Nix text, enumerates all interesting cursor
// positions from the source map, then calls each position-taking LSP feature
// and asserts it doesn't panic. No type-correctness assertions — just crash
// freedom.

use proptest::prelude::*;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Position, Range};

use crate::completion::completion;
use crate::document_highlight::document_highlight;
use crate::document_link::document_links;
use crate::document_symbol::document_symbols;
use crate::goto_def::goto_definition;
use crate::hover::hover;
use crate::inlay_hint::inlay_hints;
use crate::references::find_references;
use crate::rename::prepare_rename;
use crate::selection_range::selection_ranges;
use crate::semantic_tokens::semantic_tokens;
use crate::signature_help::signature_help;
use crate::test_util::{interesting_positions, TestAnalysis};
use lang_check::aliases::DocIndex;

// ==============================================================================
// Nix text generators
// ==============================================================================
//
// Simple template-based generators that produce diverse, valid Nix covering
// all syntax forms. Intentionally simpler than lang_check's generators — no
// type tracking, just syntax coverage.

fn arb_ident() -> impl Strategy<Value = String> {
    "_pbt_[a-z]{1,6}".prop_map(|s| s)
}

fn arb_int() -> impl Strategy<Value = String> {
    (1..1000i64).prop_map(|n| n.to_string())
}

fn arb_float() -> impl Strategy<Value = String> {
    (1..1000i64).prop_map(|n| format!("{n}.0"))
}

fn arb_bool() -> impl Strategy<Value = String> {
    prop_oneof![Just("true".to_string()), Just("false".to_string()),]
}

fn arb_string_lit() -> impl Strategy<Value = String> {
    "[a-z]{0,10}".prop_map(|s| format!("\"{s}\""))
}

fn arb_null() -> impl Strategy<Value = String> {
    Just("null".to_string())
}

fn arb_literal() -> impl Strategy<Value = String> {
    prop_oneof![
        arb_int(),
        arb_float(),
        arb_bool(),
        arb_string_lit(),
        arb_null(),
    ]
}

/// `let <id> = <val>; in <id>`
fn arb_let_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_literal()).prop_map(|(id, val)| format!("let {id} = {val}; in {id}"))
}

/// `<id>: <body>` — simple lambda
fn arb_lambda_simple() -> impl Strategy<Value = String> {
    (arb_ident(), arb_literal()).prop_map(|(param, body)| format!("{param}: {body}"))
}

/// `{ <id>, ... }: <body>` — pattern lambda
fn arb_lambda_pattern() -> impl Strategy<Value = String> {
    (arb_ident(), arb_ident()).prop_map(|(p1, p2)| format!("{{ {p1}, {p2} ? 0, ... }}: {p1}"))
}

fn arb_lambda_expr() -> impl Strategy<Value = String> {
    prop_oneof![arb_lambda_simple(), arb_lambda_pattern(),]
}

/// `{ <id> = <val>; ... }`
fn arb_attrset_expr() -> impl Strategy<Value = String> {
    proptest::collection::vec((arb_ident(), arb_literal()), 1..=4).prop_map(|fields| {
        let body: String = fields.iter().map(|(k, v)| format!("{k} = {v}; ")).collect();
        format!("{{ {body}}}")
    })
}

/// `if <cond> then <then> else <else>`
fn arb_if_expr() -> impl Strategy<Value = String> {
    (arb_literal(), arb_literal())
        .prop_map(|(then_val, else_val)| format!("if true then {then_val} else {else_val}"))
}

/// `(<attrset>).<key>` — select expression
fn arb_select_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_literal()).prop_map(|(key, val)| format!("({{ {key} = {val}; }}).{key}"))
}

/// `[ <vals> ]` — list expression
fn arb_list_expr() -> impl Strategy<Value = String> {
    proptest::collection::vec(arb_literal(), 0..=4)
        .prop_map(|elems| format!("[ {} ]", elems.join(" ")))
}

/// `with <attrset>; <body>`
fn arb_with_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_literal())
        .prop_map(|(name, val)| format!("with {{ {name} = {val}; }}; {name}"))
}

/// `let <id> = <val>; in if <cond> then <id> else <id>` — tests narrowing paths
fn arb_narrowing_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_literal()).prop_map(|(id, val)| {
        format!("let {id} = {val}; in if builtins.isString {id} then {id} else {id}")
    })
}

/// `rec { <id> = <val>; <id2> = <id>; }` — recursive attrset
fn arb_rec_attrset_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_ident(), arb_literal())
        .prop_map(|(id1, id2, val)| format!("rec {{ {id1} = {val}; {id2} = {id1}; }}"))
}

/// `assert <cond>; <body>`
fn arb_assert_expr() -> impl Strategy<Value = String> {
    arb_literal().prop_map(|val| format!("assert true; {val}"))
}

/// String interpolation: `"hello ${{<expr>}}"`
fn arb_interpolation_expr() -> impl Strategy<Value = String> {
    arb_int().prop_map(|n| format!("\"result: ${{{n}}}\""))
}

/// `let <id> = <val>; in <id> + <val>` — binary operations
fn arb_binop_expr() -> impl Strategy<Value = String> {
    (arb_ident(), arb_int(), arb_int())
        .prop_map(|(id, v1, v2)| format!("let {id} = {v1}; in {id} + {v2}"))
}

/// Combine all generators with optional nesting. Each leaf form gets
/// roughly equal weight; a small fraction produces two-level nesting
/// via `let x = <inner>; in x`.
fn arb_nix_source() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        2 => arb_let_expr(),
        2 => arb_lambda_expr(),
        2 => arb_attrset_expr(),
        1 => arb_if_expr(),
        1 => arb_select_expr(),
        1 => arb_list_expr(),
        1 => arb_with_expr(),
        1 => arb_narrowing_expr(),
        1 => arb_rec_attrset_expr(),
        1 => arb_assert_expr(),
        1 => arb_interpolation_expr(),
        1 => arb_binop_expr(),
        2 => arb_literal(),
    ];

    // Wrap ~30% of leaves in a let-binding for one level of nesting.
    prop_oneof![
        7 => leaf.clone(),
        3 => (arb_ident(), leaf).prop_map(|(id, inner)| {
            format!("let {id} = {inner}; in {id}")
        }),
    ]
}

// ==============================================================================
// Crash-freedom properties
// ==============================================================================

/// Default case count for LSP PBT. Override with `PROPTEST_CASES=N`.
fn pbt_config() -> ProptestConfig {
    ProptestConfig {
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(128),
        ..ProptestConfig::default()
    }
}

proptest! {
    #![proptest_config(pbt_config())]

    // -------------------------------------------------------------------------
    // Position-probing tests: for each generated source, enumerate all
    // interesting positions and call each LSP feature at every position.
    // -------------------------------------------------------------------------

    #[test]
    fn pbt_hover_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let positions = interesting_positions(analysis, &t.root);
        let docs = DocIndex::default();
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = hover(analysis, pos, &t.root, &docs);
        }
    }

    #[test]
    fn pbt_goto_definition_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let uri = t.uri();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = goto_definition(&t.state, analysis, pos, &uri, &t.root);
        }
    }

    #[test]
    fn pbt_completion_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let docs = DocIndex::default();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = completion(analysis, pos, &t.root, &docs);
        }
    }

    #[test]
    fn pbt_references_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let uri = t.uri();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = find_references(analysis, pos, &uri, &t.root, true);
        }
    }

    #[test]
    fn pbt_document_highlight_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = document_highlight(analysis, pos, &t.root);
        }
    }

    #[test]
    fn pbt_prepare_rename_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = prepare_rename(analysis, pos, &t.root);
        }
    }

    #[test]
    fn pbt_signature_help_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = signature_help(analysis, pos, &t.root);
        }
    }

    #[test]
    fn pbt_selection_range_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let positions = interesting_positions(analysis, &t.root);
        for ip in &positions {
            let pos = analysis.line_index.position(ip.byte_offset());
            let _ = selection_ranges(analysis, vec![pos], &t.root);
        }
    }

    // -------------------------------------------------------------------------
    // Whole-file tests: no cursor position needed, just source diversity.
    // -------------------------------------------------------------------------

    #[test]
    fn pbt_semantic_tokens_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let _ = semantic_tokens(analysis, &t.root);
    }

    #[test]
    fn pbt_inlay_hints_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let root_syntax = t.root.syntax();
        let text = root_syntax.to_string();
        // Full file range: line 0 col 0 to a generous end.
        let end_line = text.lines().count().saturating_sub(1) as u32;
        let end_col = text.lines().last().map_or(0, |l: &str| l.len()) as u32;
        let full_range = Range::new(Position::new(0, 0), Position::new(end_line, end_col));
        let _ = inlay_hints(analysis, full_range, &t.root);
    }

    #[test]
    fn pbt_document_symbols_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let _ = document_symbols(analysis, &t.root);
    }

    #[test]
    fn pbt_document_links_no_crash(src in arb_nix_source()) {
        let t = TestAnalysis::new(&src);
        let analysis = t.analysis();
        let _ = document_links(analysis, &t.root);
    }
}
