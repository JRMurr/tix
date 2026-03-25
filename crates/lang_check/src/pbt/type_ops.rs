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

// Param/Return on inline type aliases with known function types.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn param_extracts_first_arg(
        param_ty in prop_oneof![Just("int"), Just("string"), Just("bool")],
        ret_ty in prop_oneof![Just("int"), Just("string"), Just("bool")],
    ) {
        // Skip when param and return are the same (can't distinguish)
        prop_assume!(param_ty != ret_ty);

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
        param_ty in prop_oneof![Just("int"), Just("string"), Just("bool")],
        ret_ty in prop_oneof![Just("int"), Just("string"), Just("bool")],
    ) {
        prop_assume!(param_ty != ret_ty);

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
