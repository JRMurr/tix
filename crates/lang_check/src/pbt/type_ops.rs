// ==============================================================================
// Property-Based Tests for Type-Level Operators
// ==============================================================================
//
// Tests typeof, Param, Return, FieldAccess, and their compositions via
// proptest. Focuses on:
// - typeof roundtrip: typeof x produces the same type as x
// - Param/Return inverse: for function types, Param and Return extract correctly
// - Composition crash-freedom: arbitrary operator chains don't panic

use proptest::prelude::*;

use crate::tests::{check_str, get_inferred_root};

/// Generate a simple Nix expression with a known primitive type.
fn arb_typed_expr() -> impl Strategy<Value = (&'static str, &'static str)> {
    prop_oneof![
        Just(("42", "int")),
        Just(("3.14", "float")),
        Just(("true", "bool")),
        Just(("\"hello\"", "string")),
        Just(("null", "null")),
    ]
}

// typeof roundtrip: the type of `typeof x` should match the type of `x`.
// We verify this by checking that annotating a binding with `typeof x`
// where x has type T, and the body also has type T, produces no errors.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn typeof_roundtrip_no_error((expr, _expected_ty) in arb_typed_expr()) {
        let src = format!(
            "let x = {expr}; /** type: y :: typeof x */ y = {expr}; in y"
        );
        let (_, result) = check_str(&src);
        prop_assert!(result.is_ok(), "typeof roundtrip should not error for: {}", expr);
    }

    // typeof roundtrip: the type of `typeof x` constrains mismatches.
    // If x is int but y's body is string, annotation should error.
    #[test]
    fn typeof_constrains_mismatch((expr, _) in arb_typed_expr()) {
        // Use a body that's definitely a different type than expr
        let mismatch_body = if expr == "\"hello\"" { "42" } else { "\"mismatch\"" };
        let src = format!(
            "let x = {expr}; /** type: y :: typeof x */ y = {mismatch_body}; in y"
        );
        let (_, result) = check_str(&src);
        prop_assert!(result.is_err(), "typeof mismatch should error: x={}, body={}", expr, mismatch_body);
    }
}

/// Generate a (param_ty, ret_ty) pair that are always distinct,
/// avoiding prop_assume! rejections that hit the global reject limit.
fn arb_distinct_type_pair() -> impl Strategy<Value = (&'static str, &'static str)> {
    static TYPES: [&str; 3] = ["int", "string", "bool"];
    // Pick an index for param, then an offset 1..3 to guarantee a different ret
    (0..3usize, 1..3usize).prop_map(|(i, off)| (TYPES[i], TYPES[(i + off) % 3]))
}

// Param/Return on inline type aliases with known function types.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn param_extracts_first_arg(
        (param_ty, ret_ty) in arb_distinct_type_pair(),
    ) {
        // Inline alias F = param_ty -> ret_ty, then Param(F) should be param_ty
        let src = format!(
            r#"/** type F = {param_ty} -> {ret_ty}; */
            let /** type: x :: Param(F) */ x = {body}; in x"#,
            body = match param_ty {
                "int" => "42",
                "string" => "\"hi\"",
                "bool" => "true",
                _ => unreachable!(),
            }
        );
        let ty = get_inferred_root(&src);
        prop_assert_eq!(format!("{ty}"), param_ty);
    }

    #[test]
    fn return_extracts_result(
        (param_ty, ret_ty) in arb_distinct_type_pair(),
    ) {
        let src = format!(
            r#"/** type F = {param_ty} -> {ret_ty}; */
            let /** type: x :: Return(F) */ x = {body}; in x"#,
            body = match ret_ty {
                "int" => "42",
                "string" => "\"hi\"",
                "bool" => "true",
                _ => unreachable!(),
            }
        );
        let ty = get_inferred_root(&src);
        prop_assert_eq!(format!("{ty}"), ret_ty);
    }
}

// Crash-freedom: random type operator chains on random types.
// We don't check correctness — just that nothing panics.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn type_op_crash_freedom(
        base_ty in prop_oneof![
            Just("int"),
            Just("string"),
            Just("int -> string"),
            Just("{ x: int, y: string }"),
        ],
        op in prop_oneof![
            Just("Param"),
            Just("Return"),
        ],
    ) {
        let src = format!(
            r#"/** type T = {base_ty}; */
            let /** type: x :: {op}(T) */ x = 42; in x"#
        );
        // Just verify no panic — result doesn't matter
        let _ = check_str(&src);
    }

    #[test]
    fn field_access_crash_freedom(
        field in prop_oneof![Just("x"), Just("y"), Just("nonexistent")],
    ) {
        let src = format!(
            r#"/** type T = {{ x: int, y: string }}; */
            let /** type: v :: T.{field} */ v = 42; in v"#
        );
        let _ = check_str(&src);
    }
}

// ==============================================================================
// PBT: resolve_export_typeof removes all TypeOf nodes
// ==============================================================================

use std::collections::HashMap;
use std::sync::Arc;

use comment_parser::ParsedTy;
use lang_ty::arena::OwnedTy;
use lang_ty::{OutputTy, PrimitiveTy, TypeArena};
use smol_str::SmolStr;

/// Generate a ParsedTy leaf that may or may not be a TypeOf.
fn arb_leaf_with_typeof() -> BoxedStrategy<(ParsedTy, Option<SmolStr>)> {
    prop_oneof![
        // Plain primitive — no typeof
        Just((ParsedTy::Primitive(PrimitiveTy::Int), None)),
        Just((ParsedTy::Primitive(PrimitiveTy::String), None)),
        Just((ParsedTy::Primitive(PrimitiveTy::Bool), None)),
        // TypeOf reference
        (0u8..5).prop_map(|i| {
            let name = SmolStr::from(format!("var{i}"));
            (ParsedTy::TypeOf(name.clone()), Some(name))
        }),
    ]
    .boxed()
}

/// Generate an attrset ParsedTy with 1-3 fields, some of which may be TypeOf.
fn arb_attrset_with_typeof() -> impl Strategy<Value = (ParsedTy, Vec<SmolStr>)> {
    prop::collection::vec((arb_leaf_with_typeof(), "[a-z]{1,4}"), 1..4).prop_map(|entries| {
        let mut fields = std::collections::BTreeMap::new();
        let mut typeof_names = Vec::new();
        for ((ty, maybe_name), field_key) in entries {
            if let Some(name) = maybe_name {
                typeof_names.push(name);
            }
            fields.insert(
                SmolStr::from(field_key),
                comment_parser::ParsedTyRef::from(ty),
            );
        }
        let attrset = ParsedTy::AttrSet(lang_ty::AttrSetTy {
            fields,
            dyn_ty: None,
            open: false,
            optional_fields: Default::default(),
        });
        (attrset, typeof_names)
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// After resolve_export_typeof, the result must contain zero TypeOf nodes.
    #[test]
    fn resolve_typeof_removes_all_typeof(
        (body, typeof_names) in arb_attrset_with_typeof(),
        export_name in "[A-Z][a-z]{2,5}",
    ) {
        let mut raw_exports = HashMap::new();
        raw_exports.insert(SmolStr::from(export_name), body);

        // Build binding_types for all typeof targets
        let mut binding_types = HashMap::new();
        for name in &typeof_names {
            let mut arena = TypeArena::new();
            let root = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            binding_types.insert(name.clone(), OwnedTy::new(Arc::new(arena), root));
        }

        let resolved = crate::resolve_export_typeof(&raw_exports, &binding_types);
        let remaining = crate::find_typeof_targets(&resolved);
        prop_assert!(
            remaining.is_empty(),
            "resolve_export_typeof should remove all TypeOf nodes, but found: {:?}",
            remaining
        );
    }
}
