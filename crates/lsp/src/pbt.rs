// ==============================================================================
// Property-based tests for LSP crash freedom
// ==============================================================================
//
// Generates structurally diverse Nix text, enumerates all interesting cursor
// positions from the source map, then calls each position-taking LSP feature
// and asserts it doesn't panic. No type-correctness assertions — just crash
// freedom.

use hegel::generators;
use hegel::TestCase;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Position, Range};

use crate::code_actions::code_actions;
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

const MAX_LITERAL_INT: i64 = 999;
const MAX_ATTR_FIELDS: usize = 4;
const MAX_LIST_ELEMS: usize = 4;
const CASES: u64 = 128;

fn ident(tc: &TestCase) -> String {
    tc.draw(generators::from_regex("_pbt_[a-z]{1,6}"))
}

fn int(tc: &TestCase) -> String {
    tc.draw(
        generators::integers::<i64>()
            .min_value(1)
            .max_value(MAX_LITERAL_INT),
    )
    .to_string()
}

fn float(tc: &TestCase) -> String {
    format!("{}.0", int(tc))
}

fn bool_lit(tc: &TestCase) -> String {
    tc.draw(generators::sampled_from(vec!["true", "false"]))
        .to_string()
}

fn string_lit(tc: &TestCase) -> String {
    let s: String = tc.draw(generators::from_regex("[a-z]{0,10}"));
    format!("\"{s}\"")
}

fn literal(tc: &TestCase) -> String {
    match tc.draw(generators::integers::<u8>().max_value(4)) {
        0 => int(tc),
        1 => float(tc),
        2 => bool_lit(tc),
        3 => string_lit(tc),
        _ => "null".to_string(),
    }
}

/// `let <id> = <val>; in <id>`
fn let_expr(tc: &TestCase) -> String {
    let (id, val) = (ident(tc), literal(tc));
    format!("let {id} = {val}; in {id}")
}

/// `<id>: <body>` — simple lambda, or `{ <id>, ... }: <body>` — pattern lambda
fn lambda_expr(tc: &TestCase) -> String {
    if tc.draw(generators::booleans()) {
        let (param, body) = (ident(tc), literal(tc));
        format!("{param}: {body}")
    } else {
        let (p1, p2) = (ident(tc), ident(tc));
        format!("{{ {p1}, {p2} ? 0, ... }}: {p1}")
    }
}

/// `{ <id> = <val>; ... }`
fn attrset_expr(tc: &TestCase) -> String {
    let n = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(MAX_ATTR_FIELDS),
    );
    let body: String = (0..n)
        .map(|_| format!("{} = {}; ", ident(tc), literal(tc)))
        .collect();
    format!("{{ {body}}}")
}

/// `if <cond> then <then> else <else>`
fn if_expr(tc: &TestCase) -> String {
    let (then_val, else_val) = (literal(tc), literal(tc));
    format!("if true then {then_val} else {else_val}")
}

/// `if true then <a> else <b>` with different-typed branches — produces a union type.
fn if_union_expr(tc: &TestCase) -> String {
    match tc.draw(generators::integers::<u8>().max_value(5)) {
        0 => r#"if true then 1 else "hello""#.to_string(),
        1 => "if true then null else 42".to_string(),
        2 => "if true then true else 1.5".to_string(),
        3 => format!("if true then {} else {}", int(tc), string_lit(tc)),
        4 => format!("if true then null else {}", bool_lit(tc)),
        // Nested: 3-way union
        _ => format!(
            "if true then {} else if true then {} else {}",
            int(tc),
            string_lit(tc),
            float(tc)
        ),
    }
}

/// `(<attrset>).<key>` — select expression
fn select_expr(tc: &TestCase) -> String {
    let (key, val) = (ident(tc), literal(tc));
    format!("({{ {key} = {val}; }}).{key}")
}

/// `[ <vals> ]` — list expression
fn list_expr(tc: &TestCase) -> String {
    let n = tc.draw(generators::integers::<usize>().max_value(MAX_LIST_ELEMS));
    let elems: Vec<String> = (0..n).map(|_| literal(tc)).collect();
    format!("[ {} ]", elems.join(" "))
}

/// `with <attrset>; <body>`
fn with_expr(tc: &TestCase) -> String {
    let (name, val) = (ident(tc), literal(tc));
    format!("with {{ {name} = {val}; }}; {name}")
}

/// `let <id> = <val>; in if <cond> then <id> else <id>` — tests narrowing paths
fn narrowing_expr(tc: &TestCase) -> String {
    let (id, val) = (ident(tc), literal(tc));
    format!("let {id} = {val}; in if builtins.isString {id} then {id} else {id}")
}

/// `rec { <id> = <val>; <id2> = <id>; }` — recursive attrset
fn rec_attrset_expr(tc: &TestCase) -> String {
    let (id1, id2, val) = (ident(tc), ident(tc), literal(tc));
    format!("rec {{ {id1} = {val}; {id2} = {id1}; }}")
}

/// `assert <cond>; <body>`
fn assert_expr(tc: &TestCase) -> String {
    format!("assert true; {}", literal(tc))
}

/// String interpolation: `"hello ${<expr>}"`
fn interpolation_expr(tc: &TestCase) -> String {
    format!("\"result: ${{{}}}\"", int(tc))
}

/// `let <id> = <val>; in <id> + <val>` — binary operations
fn binop_expr(tc: &TestCase) -> String {
    let (id, v1, v2) = (ident(tc), int(tc), int(tc));
    format!("let {id} = {v1}; in {id} + {v2}")
}

/// One leaf form. Weights: 2 let / 2 lambda / 2 attrset / 1 each of the
/// rest / 2 literal.
fn leaf(tc: &TestCase) -> String {
    match tc.draw(generators::integers::<u8>().max_value(17)) {
        0..=1 => let_expr(tc),
        2..=3 => lambda_expr(tc),
        4..=5 => attrset_expr(tc),
        6 => if_expr(tc),
        7 => if_union_expr(tc),
        8 => select_expr(tc),
        9 => list_expr(tc),
        10 => with_expr(tc),
        11 => narrowing_expr(tc),
        12 => rec_attrset_expr(tc),
        13 => assert_expr(tc),
        14 => interpolation_expr(tc),
        15 => binop_expr(tc),
        _ => literal(tc),
    }
}

/// All leaf forms, with ~30% wrapped in a let-binding for one level of nesting.
#[hegel::composite]
fn nix_source(tc: &TestCase) -> String {
    let inner = leaf(tc);
    if tc.draw(generators::weighted_booleans(0.3)) {
        let id = ident(tc);
        format!("let {id} = {inner}; in {id}")
    } else {
        inner
    }
}

// ==============================================================================
// Crash-freedom properties
// ==============================================================================
//
// Position-probing tests: for each generated source, enumerate all
// interesting positions and call each LSP feature at every position.
// Whole-file tests need no cursor position, just source diversity.
// Case count: `CASES`, overridable with `HEGEL_TEST_CASES=N`.

#[hegel::test(test_cases = CASES)]
fn pbt_hover_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    let docs = DocIndex::default();
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = hover(&snapshot, pos, &t.root, &docs);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_goto_definition_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let uri = t.uri();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = goto_definition(&t.state.registry, &snapshot, pos, &uri, &t.root);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_completion_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let docs = DocIndex::default();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = completion(
            &snapshot,
            pos,
            &t.root,
            &docs,
            &snapshot.syntax.line_index,
            None,
        );
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_references_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let uri = t.uri();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = find_references(&snapshot, pos, &uri, &t.root, true);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_document_highlight_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = document_highlight(&snapshot, pos, &t.root);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_prepare_rename_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = prepare_rename(&snapshot, pos, &t.root);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_signature_help_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = signature_help(&snapshot, pos, &t.root);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_selection_range_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let _ = selection_ranges(&snapshot, vec![pos], &t.root);
    }
}

#[hegel::test(test_cases = CASES)]
fn pbt_semantic_tokens_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let snapshot = t.snapshot();
    let _ = semantic_tokens(&snapshot, &t.root);
}

#[hegel::test(test_cases = CASES)]
fn pbt_inlay_hints_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let snapshot = t.snapshot();
    let root_syntax = t.root.syntax();
    let text = root_syntax.to_string();
    // Full file range: line 0 col 0 to a generous end.
    let end_line = text.lines().count().saturating_sub(1) as u32;
    let end_col = text.lines().last().map_or(0, |l: &str| l.len()) as u32;
    let full_range = Range::new(Position::new(0, 0), Position::new(end_line, end_col));
    let _ = inlay_hints(&snapshot, full_range, &t.root);
}

#[hegel::test(test_cases = CASES)]
fn pbt_document_symbols_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let snapshot = t.snapshot();
    let _ = document_symbols(&snapshot, &t.root);
}

#[hegel::test(test_cases = CASES)]
fn pbt_document_links_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let snapshot = t.snapshot();
    let _ = document_links(&snapshot, &t.root);
}

#[hegel::test(test_cases = CASES)]
fn pbt_code_actions_no_crash(tc: TestCase) {
    let src = tc.draw(nix_source());
    let t = TestAnalysis::new(&src);
    let analysis = t.analysis();
    let snapshot = t.snapshot();
    let positions = interesting_positions(analysis, &t.root);
    for ip in &positions {
        let pos = snapshot.syntax.line_index.position(ip.byte_offset());
        let range = Range::new(pos, pos);
        let params = tower_lsp::lsp_types::CodeActionParams {
            text_document: tower_lsp::lsp_types::TextDocumentIdentifier { uri: t.uri() },
            range,
            context: tower_lsp::lsp_types::CodeActionContext {
                diagnostics: vec![],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let _ = code_actions(&snapshot, &params, &t.root);
    }
}
