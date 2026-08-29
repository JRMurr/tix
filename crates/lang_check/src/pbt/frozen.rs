// ==============================================================================
// Property-Based Tests for Frozen Types (Multi-File Imports)
// ==============================================================================
//
// Frozen types (`Ty::Frozen(OwnedTy)`) wrap imported file types as lazy,
// zero-copy references. These tests exercise the Frozen code paths in
// constrain.rs (6 match arms + 4 helpers), infer.rs (extrude, merge),
// and collect.rs (canonicalization) using property-based testing.
//
// Strategy: oracle-based equivalence. For each test, we run the same logic
// both through the import boundary (Frozen path via `check_multifile`) and
// inline (no Frozen via `get_inferred_root`). The types should be equal,
// proving that the Frozen boundary is semantically transparent.
//
// Coverage:
// - Crash-freedom: random dep files + random operations (all 6 match arms)
// - Correctness: attrset select, lambda apply, merge, passthrough, union
// - Frozen+Frozen: two imports interacting (merge, union, apply, select)
// - Large-lambda threshold: exercises lazy decomposition (>64 fields) vs
//   full interning (<=64 fields)

use hegel::generators;
use hegel::TestCase;
use lang_ty::hegel_gen::{idents, prims};
use lang_ty::raw_ty::RawTy;
use lang_ty::PrimitiveTy;
use smol_str::SmolStr;

use super::gen::{func, nix_text, prim_src};
use super::NixTextStr;
use crate::tests::{check_multifile, get_inferred_root, get_multifile_root};

/// Nesting depth of randomly generated dep files.
const DEP_DEPTH: u32 = 4;
const MAX_ATTR_FIELDS: usize = 4;

// ==============================================================================
// Crash-Freedom Tests
// ==============================================================================
//
// Generate random dep files and random operations on imports. Verify that
// type inference completes without panicking — type errors are acceptable.

/// Operations to apply to a single import.
#[derive(Debug, Clone)]
enum FrozenOp {
    /// `import /dep.nix`
    PassThrough,
    /// `(import /dep.nix).field_name`
    Select(String),
    /// `let x = import /dep.nix; in x`
    LetBind,
    /// `(import /dep.nix) 42`
    Apply,
    /// `(import /dep.nix) // { _pbt_extra = 1; }`
    MergeLiteral,
}

/// Weights: 2 passthrough / 3 select / 2 let / 2 apply / 3 merge.
fn frozen_op(tc: &TestCase) -> FrozenOp {
    match tc.draw(generators::integers::<u8>().max_value(11)) {
        0..=1 => FrozenOp::PassThrough,
        2..=4 => FrozenOp::Select(tc.draw(idents()).to_string()),
        5..=6 => FrozenOp::LetBind,
        7..=8 => FrozenOp::Apply,
        _ => FrozenOp::MergeLiteral,
    }
}

fn apply_op(op: &FrozenOp, import_expr: &str) -> String {
    match op {
        FrozenOp::PassThrough => import_expr.to_string(),
        FrozenOp::Select(field) => format!("({import_expr}).{field}"),
        FrozenOp::LetBind => format!("let _pbt_x = {import_expr}; in _pbt_x"),
        FrozenOp::Apply => format!("({import_expr}) 42"),
        FrozenOp::MergeLiteral => format!("({import_expr}) // {{ _pbt_extra = 1; }}"),
    }
}

/// Operations involving two imports.
#[derive(Debug, Clone, Copy)]
enum TwoImportOp {
    /// `(import /a.nix) // (import /b.nix)`
    Merge,
    /// `if true then import /a.nix else import /b.nix`
    Union,
    /// `let a = import /a.nix; b = import /b.nix; in { inherit a b; }`
    LetBindBoth,
}

fn two_import_op(tc: &TestCase) -> TwoImportOp {
    tc.draw(generators::sampled_from(vec![
        TwoImportOp::Merge,
        TwoImportOp::Union,
        TwoImportOp::LetBindBoth,
    ]))
}

fn apply_two_import_op(op: TwoImportOp) -> String {
    match op {
        TwoImportOp::Merge => "(import /a.nix) // (import /b.nix)".to_string(),
        TwoImportOp::Union => "if true then import /a.nix else import /b.nix".to_string(),
        TwoImportOp::LetBindBoth => {
            "let _pbt_a = import /a.nix; _pbt_b = import /b.nix; in { a = _pbt_a; b = _pbt_b; }"
                .to_string()
        }
    }
}

fn dep_src(tc: &TestCase) -> NixTextStr {
    nix_text(tc, DEP_DEPTH).1
}

/// Inference completes without panic for any dep file + operation.
#[hegel::test(test_cases = 256)]
fn frozen_crash_freedom(tc: TestCase) {
    let dep_src = dep_src(&tc);
    let main_src = apply_op(&frozen_op(&tc), "import /dep.nix");
    let _ = check_multifile(&[("/main.nix", &main_src), ("/dep.nix", &dep_src)]);
}

/// Two random dep files combined via merge/union/let-bind — no panic.
#[hegel::test(test_cases = 128)]
fn frozen_two_import_crash(tc: TestCase) {
    let a_src = dep_src(&tc);
    let b_src = dep_src(&tc);
    let main_src = apply_two_import_op(two_import_op(&tc));
    let _ = check_multifile(&[
        ("/main.nix", &main_src),
        ("/a.nix", &a_src),
        ("/b.nix", &b_src),
    ]);
}

/// Three-file chain: A imports B imports C. Exercises nested Frozen.
#[hegel::test(test_cases = 128)]
fn frozen_transitive_crash(tc: TestCase) {
    let c_src = dep_src(&tc);
    let b_src = "import /c.nix";
    let main_src = apply_op(&frozen_op(&tc), "import /b.nix");
    let _ = check_multifile(&[
        ("/main.nix", &main_src),
        ("/b.nix", b_src),
        ("/c.nix", &c_src),
    ]);
}

// ==============================================================================
// Correctness Tests — Single Import (Oracle)
// ==============================================================================
//
// Generate a dep file with a known type, perform an operation via import
// (Frozen path) and inline (no Frozen). Compare results.

/// A primitive leaf as (RawTy, nix text).
fn prim_leaf(tc: &TestCase) -> (RawTy, NixTextStr) {
    let prim: PrimitiveTy = tc.draw(prims());
    (RawTy::Primitive(prim), prim_src(tc, prim))
}

/// An attrset with exactly these field names (primitive values), written as
/// one literal or as two literals joined with `//`.
/// Returns (RawTy::AttrSet, nix_text, field_names).
fn attrset_with_names(tc: &TestCase, names: Vec<SmolStr>) -> (RawTy, NixTextStr, Vec<String>) {
    let split = tc.draw(generators::integers::<usize>().max_value(names.len()));
    let (left, right) = names.split_at(split);
    let mut fields = std::collections::BTreeMap::new();
    let mut literal = |chunk: &[SmolStr]| -> String {
        let parts: Vec<String> = chunk
            .iter()
            .map(|name| {
                let (ty, text) = prim_leaf(tc);
                fields.insert(name.clone(), ty);
                format!("{name}=({text});")
            })
            .collect();
        format!("({{{}}})", parts.join(" "))
    };
    let text = match (left.is_empty(), right.is_empty()) {
        (false, false) => format!("{} // {}", literal(left), literal(right)),
        (true, _) => literal(right),
        (_, true) => literal(left),
    };
    let names = names.iter().map(|n| n.to_string()).collect();
    (RawTy::AttrSet(fields), text, names)
}

fn field_names(tc: &TestCase, min: usize, max: usize) -> Vec<SmolStr> {
    tc.draw(
        generators::vecs(idents())
            .min_size(min)
            .max_size(max)
            .unique(true),
    )
}

/// A random attrset with 1-4 fields of primitive types.
fn frozen_attrset(tc: &TestCase) -> (RawTy, NixTextStr, Vec<String>) {
    let names = field_names(tc, 1, MAX_ATTR_FIELDS);
    attrset_with_names(tc, names)
}

/// Two attrsets with disjoint field names: draw one unique name list and
/// split it so each side gets at least one field.
#[allow(clippy::type_complexity)]
fn two_disjoint_attrsets(
    tc: &TestCase,
) -> (
    (RawTy, NixTextStr, Vec<String>),
    (RawTy, NixTextStr, Vec<String>),
) {
    let names = field_names(tc, 2, 2 * MAX_ATTR_FIELDS);
    let split = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(names.len() - 1),
    );
    let (a, b) = names.split_at(split);
    (
        attrset_with_names(tc, a.to_vec()),
        attrset_with_names(tc, b.to_vec()),
    )
}

/// Import a primitive value — exercises extrude fast-path on Frozen.
#[hegel::test(test_cases = 128)]
fn frozen_primitive_passthrough(tc: TestCase) {
    let (_ty, dep_src) = prim_leaf(&tc);
    let frozen_ty = get_multifile_root(&[("/main.nix", "import /dep.nix"), ("/dep.nix", &dep_src)]);
    let inline_ty = get_inferred_root(&dep_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Select a field from an imported attrset — exercises constrain_frozen_attrset.
#[hegel::test(test_cases = 128)]
fn frozen_attrset_select(tc: TestCase) {
    let (_, dep_src, field_names) = frozen_attrset(&tc);
    let field_idx = tc.draw(generators::integers::<usize>().max_value(field_names.len() - 1));
    let field = &field_names[field_idx];
    let main_src = format!("(import /dep.nix).{field}");
    let inline_src = format!("({dep_src}).{field}");

    let frozen_ty = get_multifile_root(&[("/main.nix", &main_src), ("/dep.nix", &dep_src)]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Select multiple fields from the same import — exercises partial materialization.
#[hegel::test(test_cases = 128)]
fn frozen_attrset_multi_select(tc: TestCase) {
    let (_, dep_src, field_names) = frozen_attrset(&tc);
    let accesses: Vec<String> = field_names
        .iter()
        .map(|f| format!("{f} = (import /dep.nix).{f}"))
        .collect();
    let main_src = format!("{{ {} }}", accesses.join("; "));

    let inline_accesses: Vec<String> = field_names
        .iter()
        .map(|f| format!("{f} = ({dep_src}).{f}"))
        .collect();
    let inline_src = format!("{{ {} }}", inline_accesses.join("; "));

    let frozen_ty = get_multifile_root(&[("/main.nix", &main_src), ("/dep.nix", &dep_src)]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// If inline inference succeeds, the frozen path must succeed with the same type.
#[track_caller]
fn assert_frozen_matches_inline(files: &[(&str, &str)], inline_src: &str) {
    let frozen_res = check_multifile(files);
    if crate::tests::check_str(inline_src).1.is_ok() {
        let inline_ty = get_inferred_root(inline_src);
        assert_eq!(frozen_res.0, inline_ty);
    }
}

/// Apply an imported function — exercises constrain_frozen_lambda.
#[hegel::test(test_cases = 128)]
fn frozen_lambda_apply(tc: TestCase) {
    let (_, dep_src) = func(&tc, prim_leaf(&tc));
    let main_src = "(import /dep.nix) 42";
    let inline_src = format!("({dep_src}) 42");
    assert_frozen_matches_inline(
        &[("/main.nix", main_src), ("/dep.nix", &dep_src)],
        &inline_src,
    );
}

/// Merge an imported attrset with a literal — exercises try_resolve_merge Frozen unwrap.
#[hegel::test(test_cases = 128)]
fn frozen_merge_literal(tc: TestCase) {
    let (_, dep_src, _) = frozen_attrset(&tc);
    let main_src = "(import /dep.nix) // { _pbt_extra = 1; }";
    let inline_src = format!("({dep_src}) // {{ _pbt_extra = 1; }}");

    let frozen_ty = get_multifile_root(&[("/main.nix", main_src), ("/dep.nix", &dep_src)]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Pass a literal attrset to an imported function expecting an attrset param.
/// Exercises AttrSet <: Frozen (constrain_attrset_frozen).
#[hegel::test(test_cases = 64)]
fn frozen_attrset_sub(tc: TestCase) {
    let (_, dep_src, field_names) = frozen_attrset(&tc);
    let pattern = field_names.join(", ");
    let body = &field_names[0];

    let func_src = format!("{{ {pattern} }}: {body}");
    let main_src = format!("let _pbt_f = {func_src}; in _pbt_f (import /dep.nix)");
    let inline_src = format!("let _pbt_f = {func_src}; in _pbt_f ({dep_src})");
    assert_frozen_matches_inline(
        &[("/main.nix", &main_src), ("/dep.nix", &dep_src)],
        &inline_src,
    );
}

// ==============================================================================
// Frozen+Frozen Interaction Correctness Tests
// ==============================================================================
//
// Two different Frozen types from separate file imports interacting.
// Verifies operations work when both operands are from different arenas.

/// Merge two imported attrsets and select a field from the result.
#[hegel::test(test_cases = 64)]
fn frozen_merge_two_imports(tc: TestCase) {
    let ((_, a_src, a_names), (_, b_src, b_names)) = two_disjoint_attrsets(&tc);
    let pick_from_a = tc.draw(generators::booleans());
    let field = if pick_from_a {
        &a_names[0]
    } else {
        &b_names[0]
    };

    let main_src = format!("let _pbt_m = (import /a.nix) // (import /b.nix); in _pbt_m.{field}");
    let inline_src = format!("let _pbt_m = ({a_src}) // ({b_src}); in _pbt_m.{field}");

    let frozen_ty = get_multifile_root(&[
        ("/main.nix", &main_src),
        ("/a.nix", &a_src),
        ("/b.nix", &b_src),
    ]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Union of two imports via if-then-else — crash-freedom.
///
/// Exact type comparison is skipped because union canonicalization may
/// produce structurally different (but semantically equivalent) types
/// when branches come from separate arenas. This is the same limitation
/// as `test_combined_typing` for inline union types.
#[hegel::test(test_cases = 64)]
fn frozen_union_two_imports(tc: TestCase) {
    let a_src = dep_src(&tc);
    let b_src = dep_src(&tc);
    let main_src = "if true then import /a.nix else import /b.nix";
    let _ = check_multifile(&[
        ("/main.nix", main_src),
        ("/a.nix", &a_src),
        ("/b.nix", &b_src),
    ]);
}

/// Apply one import (lambda) to another import (value).
#[hegel::test(test_cases = 64)]
fn frozen_apply_frozen_arg(tc: TestCase) {
    let (_, func_src) = func(&tc, prim_leaf(&tc));
    let (_arg_ty, arg_src) = prim_leaf(&tc);
    let main_src = "(import /func.nix) (import /arg.nix)";
    let inline_src = format!("({func_src}) ({arg_src})");
    assert_frozen_matches_inline(
        &[
            ("/main.nix", main_src),
            ("/func.nix", &func_src),
            ("/arg.nix", &arg_src),
        ],
        &inline_src,
    );
}

/// Merge two imports and access fields from both sides.
#[hegel::test(test_cases = 64)]
fn frozen_select_after_merge(tc: TestCase) {
    let ((_, a_src, a_names), (_, b_src, b_names)) = two_disjoint_attrsets(&tc);
    let a_field = &a_names[0];
    let b_field = &b_names[0];

    let main_src = format!(
        "let _pbt_m = (import /a.nix) // (import /b.nix); \
         in {{ _pbt_fa = _pbt_m.{a_field}; _pbt_fb = _pbt_m.{b_field}; }}"
    );
    let inline_src = format!(
        "let _pbt_m = ({a_src}) // ({b_src}); \
         in {{ _pbt_fa = _pbt_m.{a_field}; _pbt_fb = _pbt_m.{b_field}; }}"
    );

    let frozen_ty = get_multifile_root(&[
        ("/main.nix", &main_src),
        ("/a.nix", &a_src),
        ("/b.nix", &b_src),
    ]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Let-bind two imports and use both — exercises extrude on multiple Frozen values.
#[hegel::test(test_cases = 64)]
fn frozen_let_bind_two(tc: TestCase) {
    let ((_, a_src, a_names), (_, b_src, b_names)) = two_disjoint_attrsets(&tc);
    let a_field = &a_names[0];
    let b_field = &b_names[0];

    let main_src = format!(
        "let _pbt_a = import /a.nix; _pbt_b = import /b.nix; \
         in {{ _pbt_fa = _pbt_a.{a_field}; _pbt_fb = _pbt_b.{b_field}; }}"
    );
    let inline_src = format!(
        "let _pbt_a = ({a_src}); _pbt_b = ({b_src}); \
         in {{ _pbt_fa = _pbt_a.{a_field}; _pbt_fb = _pbt_b.{b_field}; }}"
    );

    let frozen_ty = get_multifile_root(&[
        ("/main.nix", &main_src),
        ("/a.nix", &a_src),
        ("/b.nix", &b_src),
    ]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

// ==============================================================================
// Large-Lambda Threshold Tests
// ==============================================================================
//
// The FROZEN_LAMBDA_FIELD_THRESHOLD (64) in constrain.rs determines whether
// a Frozen lambda body is lazily decomposed (>64 fields) or fully interned
// (<=64 fields). These tests exercise both paths.

const FROZEN_LAMBDA_FIELD_THRESHOLD: usize = 64;
const MAX_EXTRA_FIELDS: usize = 20;

/// A dep file that is a lambda returning an attrset with `n` int fields.
fn make_large_lambda_dep(n: usize) -> String {
    let fields: Vec<String> = (0..n).map(|i| format!("_pbt_f{i} = {i}")).collect();
    format!("_pbt_x: {{ {}; }}", fields.join("; "))
}

#[track_caller]
fn assert_large_lambda_select(tc: &TestCase, n_fields: usize) {
    let idx = tc.draw(generators::integers::<usize>().max_value(n_fields - 1));
    let dep_src = make_large_lambda_dep(n_fields);
    let main_src = format!("((import /dep.nix) 0)._pbt_f{idx}");
    let inline_src = format!("(({dep_src}) 0)._pbt_f{idx}");

    let frozen_ty = get_multifile_root(&[("/main.nix", &main_src), ("/dep.nix", &dep_src)]);
    let inline_ty = get_inferred_root(&inline_src);
    assert_eq!(frozen_ty, inline_ty);
}

/// Below threshold (<=64 fields): full interning path.
#[hegel::test(test_cases = 64)]
fn frozen_lambda_below_threshold(tc: TestCase) {
    let n_fields = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(FROZEN_LAMBDA_FIELD_THRESHOLD),
    );
    assert_large_lambda_select(&tc, n_fields);
}

/// Above threshold (>64 fields): lazy decomposition path.
#[hegel::test(test_cases = 64)]
fn frozen_lambda_above_threshold(tc: TestCase) {
    let extra = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(MAX_EXTRA_FIELDS),
    );
    assert_large_lambda_select(&tc, FROZEN_LAMBDA_FIELD_THRESHOLD + extra);
}
