// ==============================================================================
// Property-Based Tests for Let-Bridged Polymorphism across File Boundaries
// ==============================================================================
//
// Fuzzes the invariant that when a lambda is valid in single-file usage, it
// must also be valid when imported from another file. The bug class targeted
// here: exported signatures losing cross-file polymorphism because
// `constrain_equal` bridges (name slots, expr slots, let-binding intermediates)
// emitted as distinct free variables in the canonicalized `OutputTy`, so
// callers could not satisfy what was logically the same variable. See commit
// 7f241f9 and `tests::null_default_polymorphic_*` example tests.
//
// Two example shapes are fuzzed directly (the user repro and a stripped-down
// identity variant), plus a baseline plain lambda as a sanity check — the
// latter ensures the harness doesn't reject valid single-file examples.

use proptest::prelude::*;

use super::arb_primitive;
use crate::aliases::TypeAliasRegistry;
use crate::diagnostic::TixDiagnosticKind;
use crate::tests::{check_multifile_with_aliases, check_str};

/// Gate on a successful single-file call, then assert the same lambda
/// imported from `/lib.nix` and applied in `/main.nix` produces no
/// `TypeMismatch` diagnostics.
fn assert_import_preserves_call(fun_text: &str, arg_text: &str) -> Result<(), TestCaseError> {
    let single_src = format!("({fun_text}) ({arg_text})");
    if check_str(&single_src).1.is_err() {
        // Single-file is already ill-typed; skip — not a useful example.
        return Ok(());
    }

    let main_src = format!("let f = import /lib.nix; in f ({arg_text})");
    let files: &[(&str, &str)] = &[("/main.nix", main_src.as_str()), ("/lib.nix", fun_text)];
    let (_root, import_errors, diagnostics) =
        check_multifile_with_aliases(files, &TypeAliasRegistry::default());

    prop_assert!(
        import_errors.is_empty(),
        "unexpected import errors: {import_errors:?}"
    );

    let type_errors: Vec<_> = diagnostics
        .iter()
        .filter(|d| matches!(d.kind, TixDiagnosticKind::TypeMismatch { .. }))
        .collect();
    prop_assert!(
        type_errors.is_empty(),
        "cross-file caller produced a type error that single-file inference did not.\nlib.nix: {fun_text}\nmain.nix: {main_src}\ntype_errors: {type_errors:#?}"
    );
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// Baseline: plain lambda that ignores its param. Imports of this shape
    /// should never regress — if this fails, the harness itself is broken.
    #[test]
    fn test_import_preserves_plain_lambda(
        (_body_ty, body_text) in arb_primitive(),
        (_arg_ty, arg_text) in arb_primitive(),
    ) {
        let fun_text = format!("(__pbt_p: {body_text})");
        assert_import_preserves_call(&fun_text, &arg_text)?;
    }

    /// Param-bridge shape: `x: let r = x; in r`. Before the EquivDsu fix,
    /// the param and body slots of the exported signature used different
    /// free-var ids, and callers could not pass any value that didn't also
    /// satisfy an accidental upper bound leaked through the expr-slot cycle.
    #[test]
    fn test_import_preserves_param_bridged_identity(
        (_arg_ty, arg_text) in arb_primitive(),
    ) {
        assert_import_preserves_call(
            "(__pbt_p: let __pbt_r = __pbt_p; in __pbt_r)",
            &arg_text,
        )?;
    }

    /// Null-default + param bridge — the exact user repro shape. Before
    /// the fix, `{ x = <non-null prim>; }` failed with "expected null, got
    /// <prim>" because the default's `null` lower bound leaked into the
    /// param's Neg position via the `constrain_equal`-linked expr slots.
    #[test]
    fn test_import_preserves_null_default_bridged(
        (_val_ty, val_text) in arb_primitive(),
    ) {
        let arg_text = format!("{{ x = {val_text}; }}");
        assert_import_preserves_call(
            "({ x ? null }: let __pbt_r = x; in __pbt_r)",
            &arg_text,
        )?;
    }
}
