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

use std::collections::HashSet;

use lang_ty::{
    arbitrary::{arb_smol_str_ident, RawTy, RecursiveParams},
    PrimitiveTy,
};
use proptest::prelude::*;

use super::{arb_nix_text, attr_strat, func_strat, prim_ty_to_string, NixTextStr};
use crate::tests::{check_multifile, get_inferred_root, get_multifile_root};

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

fn arb_frozen_op() -> impl Strategy<Value = FrozenOp> {
    prop_oneof![
        2 => Just(FrozenOp::PassThrough),
        3 => arb_smol_str_ident().prop_map(|s| FrozenOp::Select(s.to_string())),
        2 => Just(FrozenOp::LetBind),
        2 => Just(FrozenOp::Apply),
        3 => Just(FrozenOp::MergeLiteral),
    ]
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
#[derive(Debug, Clone)]
enum TwoImportOp {
    /// `(import /a.nix) // (import /b.nix)`
    Merge,
    /// `if true then import /a.nix else import /b.nix`
    Union,
    /// `let a = import /a.nix; b = import /b.nix; in { inherit a b; }`
    LetBindBoth,
}

fn arb_two_import_op() -> impl Strategy<Value = TwoImportOp> {
    prop_oneof![
        Just(TwoImportOp::Merge),
        Just(TwoImportOp::Union),
        Just(TwoImportOp::LetBindBoth),
    ]
}

fn apply_two_import_op(op: &TwoImportOp) -> String {
    match op {
        TwoImportOp::Merge => "(import /a.nix) // (import /b.nix)".to_string(),
        TwoImportOp::Union => "if true then import /a.nix else import /b.nix".to_string(),
        TwoImportOp::LetBindBoth => {
            "let _pbt_a = import /a.nix; _pbt_b = import /b.nix; in { a = _pbt_a; b = _pbt_b; }"
                .to_string()
        }
    }
}

fn default_params() -> RecursiveParams {
    RecursiveParams {
        depth: 4,
        desired_size: 64,
        expected_branch_size: 3,
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    /// Inference completes without panic for any dep file + operation.
    #[test]
    fn frozen_crash_freedom(
        (_dep_ty, dep_src) in arb_nix_text(default_params()),
        op in arb_frozen_op(),
    ) {
        let main_src = apply_op(&op, "import /dep.nix");
        let _ = check_multifile(&[("/main.nix", &main_src), ("/dep.nix", &dep_src)]);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128, .. ProptestConfig::default()
    })]

    /// Two random dep files combined via merge/union/let-bind — no panic.
    #[test]
    fn frozen_two_import_crash(
        (_a_ty, a_src) in arb_nix_text(default_params()),
        (_b_ty, b_src) in arb_nix_text(default_params()),
        op in arb_two_import_op(),
    ) {
        let main_src = apply_two_import_op(&op);
        let _ = check_multifile(&[
            ("/main.nix", &main_src),
            ("/a.nix", &a_src),
            ("/b.nix", &b_src),
        ]);
    }

    /// Three-file chain: A imports B imports C. Exercises nested Frozen.
    #[test]
    fn frozen_transitive_crash(
        (_c_ty, c_src) in arb_nix_text(default_params()),
        op in arb_frozen_op(),
    ) {
        let b_src = "import /c.nix";
        let main_src = apply_op(&op, "import /b.nix");
        let _ = check_multifile(&[
            ("/main.nix", &main_src),
            ("/b.nix", b_src),
            ("/c.nix", &c_src),
        ]);
    }
}

// ==============================================================================
// Correctness Tests — Single Import (Oracle)
// ==============================================================================
//
// Generate a dep file with a known type, perform an operation via import
// (Frozen path) and inline (no Frozen). Compare results.

/// Leaf strategy producing (RawTy, NixTextStr) for primitive types.
fn arb_prim_leaf() -> BoxedStrategy<(RawTy, NixTextStr)> {
    any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(RawTy::Primitive(prim)), prim_ty_to_string(prim)))
        .boxed()
}

/// Generate a random attrset with 1-4 fields of primitive types.
/// Returns (RawTy::AttrSet, nix_text, field_names).
fn arb_frozen_attrset() -> impl Strategy<Value = (RawTy, NixTextStr, Vec<String>)> {
    attr_strat(arb_prim_leaf()).prop_filter_map(
        "need non-empty attrset with known fields",
        |(ty, text)| {
            if let RawTy::AttrSet(ref fields) = ty {
                let names: Vec<String> = fields.keys().map(|k| k.to_string()).collect();
                if names.is_empty() {
                    return None;
                }
                Some((ty, text, names))
            } else {
                None
            }
        },
    )
}

/// Generate two attrsets with disjoint field names.
fn arb_two_disjoint_attrsets() -> impl Strategy<
    Value = (
        (RawTy, NixTextStr, Vec<String>),
        (RawTy, NixTextStr, Vec<String>),
    ),
> {
    (arb_frozen_attrset(), arb_frozen_attrset()).prop_filter(
        "need disjoint field names",
        |((_, _, a_names), (_, _, b_names))| {
            let a_set: HashSet<_> = a_names.iter().collect();
            b_names.iter().all(|n| !a_set.contains(n))
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128, .. ProptestConfig::default()
    })]

    /// Import a primitive value — exercises extrude fast-path on Frozen.
    #[test]
    fn frozen_primitive_passthrough((_ty, dep_src) in arb_prim_leaf()) {
        let frozen_ty = get_multifile_root(&[
            ("/main.nix", "import /dep.nix"),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&dep_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }

    /// Select a field from an imported attrset — exercises constrain_frozen_attrset.
    #[test]
    fn frozen_attrset_select(
        (_, dep_src, field_names) in arb_frozen_attrset(),
        field_idx in any::<prop::sample::Index>(),
    ) {
        let field = &field_names[field_idx.index(field_names.len())];
        let main_src = format!("(import /dep.nix).{field}");
        let inline_src = format!("({dep_src}).{field}");

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", &main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }

    /// Select multiple fields from the same import — exercises partial materialization.
    #[test]
    fn frozen_attrset_multi_select(
        (_, dep_src, field_names) in arb_frozen_attrset(),
    ) {
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

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", &main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128, .. ProptestConfig::default()
    })]

    /// Apply an imported function — exercises constrain_frozen_lambda.
    #[test]
    fn frozen_lambda_apply(
        (_, dep_src) in func_strat(arb_prim_leaf()),
    ) {
        let main_src = "(import /dep.nix) 42";
        let inline_src = format!("({dep_src}) 42");

        let frozen_res = check_multifile(&[
            ("/main.nix", main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_res = crate::tests::check_str(&inline_src);

        // If inline succeeds, frozen should too and types should match.
        if inline_res.1.is_ok() {
            let frozen_ty = frozen_res.0;
            let inline_ty = get_inferred_root(&inline_src);
            prop_assert_eq!(frozen_ty, inline_ty);
        }
    }

    /// Merge an imported attrset with a literal — exercises try_resolve_merge Frozen unwrap.
    #[test]
    fn frozen_merge_literal(
        (_, dep_src, _) in arb_frozen_attrset(),
    ) {
        let main_src = "(import /dep.nix) // { _pbt_extra = 1; }";
        let inline_src = format!("({dep_src}) // {{ _pbt_extra = 1; }}");

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64, .. ProptestConfig::default()
    })]

    /// Pass a literal attrset to an imported function expecting an attrset param.
    /// Exercises AttrSet <: Frozen (constrain_attrset_frozen).
    #[test]
    fn frozen_attrset_sub(
        (_, dep_src, field_names) in arb_frozen_attrset(),
    ) {
        let params: Vec<String> = field_names.iter().map(|f| f.to_string()).collect();
        let pattern = params.join(", ");
        let body = if params.is_empty() {
            "0".to_string()
        } else {
            params[0].clone()
        };

        let func_src = format!("{{ {pattern} }}: {body}");
        let call_src = dep_src.clone();

        let main_src = format!("let _pbt_f = {func_src}; in _pbt_f (import /dep.nix)");
        let inline_src = format!("let _pbt_f = {func_src}; in _pbt_f ({call_src})");

        let frozen_res = check_multifile(&[
            ("/main.nix", &main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_res = crate::tests::check_str(&inline_src);

        if inline_res.1.is_ok() {
            let frozen_ty = frozen_res.0;
            let inline_ty = get_inferred_root(&inline_src);
            prop_assert_eq!(frozen_ty, inline_ty);
        }
    }
}

// ==============================================================================
// Frozen+Frozen Interaction Correctness Tests
// ==============================================================================
//
// Two different Frozen types from separate file imports interacting.
// Verifies operations work when both operands are from different arenas.

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_local_rejects: 100_000,
        .. ProptestConfig::default()
    })]

    /// Merge two imported attrsets and select a field from the result.
    #[test]
    fn frozen_merge_two_imports(
        ((_, a_src, a_names), (_, b_src, b_names)) in arb_two_disjoint_attrsets(),
        pick_from_a in any::<bool>(),
    ) {
        let field = if pick_from_a {
            &a_names[0]
        } else {
            &b_names[0]
        };

        let main_src = format!(
            "let _pbt_m = (import /a.nix) // (import /b.nix); in _pbt_m.{field}"
        );
        let inline_src = format!(
            "let _pbt_m = ({a_src}) // ({b_src}); in _pbt_m.{field}"
        );

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", &main_src),
            ("/a.nix", &a_src),
            ("/b.nix", &b_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }

    /// Union of two imports via if-then-else — crash-freedom.
    ///
    /// Exact type comparison is skipped because union canonicalization may
    /// produce structurally different (but semantically equivalent) types
    /// when branches come from separate arenas. This is the same limitation
    /// as `test_combined_typing` for inline union types.
    #[test]
    fn frozen_union_two_imports(
        (_a_ty, a_src) in arb_nix_text(default_params()),
        (_b_ty, b_src) in arb_nix_text(default_params()),
    ) {
        let main_src = "if true then import /a.nix else import /b.nix";
        let _ = check_multifile(&[
            ("/main.nix", main_src),
            ("/a.nix", &a_src),
            ("/b.nix", &b_src),
        ]);
    }

    /// Apply one import (lambda) to another import (value).
    #[test]
    fn frozen_apply_frozen_arg(
        (_, func_src) in func_strat(arb_prim_leaf()),
        (_arg_ty, arg_src) in arb_prim_leaf(),
    ) {
        let main_src = "(import /func.nix) (import /arg.nix)";
        let inline_src = format!("({func_src}) ({arg_src})");

        let frozen_res = check_multifile(&[
            ("/main.nix", main_src),
            ("/func.nix", &func_src),
            ("/arg.nix", &arg_src),
        ]);
        let inline_res = crate::tests::check_str(&inline_src);

        if inline_res.1.is_ok() {
            let frozen_ty = frozen_res.0;
            let inline_ty = get_inferred_root(&inline_src);
            prop_assert_eq!(frozen_ty, inline_ty);
        }
    }

    /// Merge two imports and access fields from both sides.
    #[test]
    fn frozen_select_after_merge(
        ((_, a_src, a_names), (_, b_src, b_names)) in arb_two_disjoint_attrsets(),
    ) {
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
        prop_assert_eq!(frozen_ty, inline_ty);
    }

    /// Let-bind two imports and use both — exercises extrude on multiple Frozen values.
    #[test]
    fn frozen_let_bind_two(
        ((_, a_src, a_names), (_, b_src, b_names)) in arb_two_disjoint_attrsets(),
    ) {
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
        prop_assert_eq!(frozen_ty, inline_ty);
    }
}

// ==============================================================================
// Large-Lambda Threshold Tests
// ==============================================================================
//
// The FROZEN_LAMBDA_FIELD_THRESHOLD (64) in constrain.rs determines whether
// a Frozen lambda body is lazily decomposed (>64 fields) or fully interned
// (<=64 fields). These tests exercise both paths.

/// Generate a dep file that is a lambda returning an attrset with `n` int fields.
fn make_large_lambda_dep(n: usize) -> String {
    let fields: Vec<String> = (0..n).map(|i| format!("_pbt_f{i} = {i}")).collect();
    format!("_pbt_x: {{ {}; }}", fields.join("; "))
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64, .. ProptestConfig::default()
    })]

    /// Below threshold (<=64 fields): full interning path.
    #[test]
    fn frozen_lambda_below_threshold(
        n_fields in 1..=64usize,
        select_idx in 0..64usize,
    ) {
        let idx = select_idx % n_fields;
        let dep_src = make_large_lambda_dep(n_fields);
        let main_src = format!("((import /dep.nix) 0)._pbt_f{}", idx);
        let inline_src = format!("(({}) 0)._pbt_f{}", dep_src, idx);

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", &main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }

    /// Above threshold (>64 fields): lazy decomposition path.
    #[test]
    fn frozen_lambda_above_threshold(
        extra in 1..=20usize,
        select_idx in 0..84usize,
    ) {
        let n_fields = 64 + extra;
        let idx = select_idx % n_fields;
        let dep_src = make_large_lambda_dep(n_fields);
        let main_src = format!("((import /dep.nix) 0)._pbt_f{}", idx);
        let inline_src = format!("(({}) 0)._pbt_f{}", dep_src, idx);

        let frozen_ty = get_multifile_root(&[
            ("/main.nix", &main_src),
            ("/dep.nix", &dep_src),
        ]);
        let inline_ty = get_inferred_root(&inline_src);
        prop_assert_eq!(frozen_ty, inline_ty);
    }
}
