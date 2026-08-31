// ==============================================================================
// Property-Based Tests for Type-Level Operators
// ==============================================================================
//
// Tests typeof, Param, Return, FieldAccess, and their compositions. Focuses on:
// - typeof roundtrip: typeof x produces the same type as x
// - Param/Return inverse: for function types, Param and Return extract correctly
// - Composition crash-freedom: arbitrary operator chains don't panic

use rustc_hash::FxHashMap as HashMap;
use std::sync::Arc;

use comment_parser::ParsedTy;
use hegel::generators;
use hegel::TestCase;
use lang_ty::arena::OwnedTy;
use lang_ty::{OutputTy, PrimitiveTy, TypeArena};
use smol_str::SmolStr;

use crate::tests::{check_str, get_inferred_root};

/// `(expr, type_name)` pairs with a known primitive type.
const TYPED_EXPRS: [(&str, &str); 5] = [
    ("42", "int"),
    ("3.14", "float"),
    ("true", "bool"),
    ("\"hello\"", "string"),
    ("null", "null"),
];

fn typed_expr(tc: &TestCase) -> (&'static str, &'static str) {
    tc.draw(generators::sampled_from(TYPED_EXPRS.to_vec()))
}

// typeof roundtrip: the type of `typeof x` should match the type of `x`.
// We verify this by checking that annotating a binding with `typeof x`
// where x has type T, and the body also has type T, produces no errors.
#[hegel::test(test_cases = 50)]
fn typeof_roundtrip_no_error(tc: TestCase) {
    let (expr, _expected_ty) = typed_expr(&tc);
    let src = format!("let x = {expr}; /** type: y :: typeof x */ y = {expr}; in y");
    let (_, result) = check_str(&src);
    assert!(
        result.is_ok(),
        "typeof roundtrip should not error for: {expr}"
    );
}

// typeof roundtrip: the type of `typeof x` constrains mismatches.
// If x is int but y's body is string, annotation should error.
#[hegel::test(test_cases = 50)]
fn typeof_constrains_mismatch(tc: TestCase) {
    let (expr, _) = typed_expr(&tc);
    // Use a body that's definitely a different type than expr
    let mismatch_body = if expr == "\"hello\"" {
        "42"
    } else {
        "\"mismatch\""
    };
    let src = format!("let x = {expr}; /** type: y :: typeof x */ y = {mismatch_body}; in y");
    let (_, result) = check_str(&src);
    assert!(
        result.is_err(),
        "typeof mismatch should error: x={expr}, body={mismatch_body}"
    );
}

const FN_TYPES: [&str; 3] = ["int", "string", "bool"];

/// A (param_ty, ret_ty) pair that are always distinct: pick an index for
/// param, then an offset 1..3 to guarantee a different ret.
fn distinct_type_pair(tc: &TestCase) -> (&'static str, &'static str) {
    let i = tc.draw(generators::integers::<usize>().max_value(FN_TYPES.len() - 1));
    let off = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(FN_TYPES.len() - 1),
    );
    (FN_TYPES[i], FN_TYPES[(i + off) % FN_TYPES.len()])
}

fn literal_of(ty: &str) -> &'static str {
    match ty {
        "int" => "42",
        "string" => "\"hi\"",
        "bool" => "true",
        _ => unreachable!(),
    }
}

// Param/Return on inline type aliases with known function types.
#[hegel::test(test_cases = 20)]
fn param_extracts_first_arg(tc: TestCase) {
    let (param_ty, ret_ty) = distinct_type_pair(&tc);
    // Inline alias F = param_ty -> ret_ty, then Param(F) should be param_ty
    let src = format!(
        r#"/** type F = {param_ty} -> {ret_ty}; */
        let /** type: x :: Param(F) */ x = {body}; in x"#,
        body = literal_of(param_ty)
    );
    let ty = get_inferred_root(&src);
    assert_eq!(format!("{ty}"), param_ty);
}

#[hegel::test(test_cases = 20)]
fn return_extracts_result(tc: TestCase) {
    let (param_ty, ret_ty) = distinct_type_pair(&tc);
    let src = format!(
        r#"/** type F = {param_ty} -> {ret_ty}; */
        let /** type: x :: Return(F) */ x = {body}; in x"#,
        body = literal_of(ret_ty)
    );
    let ty = get_inferred_root(&src);
    assert_eq!(format!("{ty}"), ret_ty);
}

// Crash-freedom: random type operator chains on random types.
// We don't check correctness — just that nothing panics.
#[hegel::test(test_cases = 100)]
fn type_op_crash_freedom(tc: TestCase) {
    let base_ty = tc.draw(generators::sampled_from(vec![
        "int",
        "string",
        "int -> string",
        "{ x: int, y: string }",
    ]));
    let op = tc.draw(generators::sampled_from(vec!["Param", "Return"]));
    let src = format!(
        r#"/** type T = {base_ty}; */
        let /** type: x :: {op}(T) */ x = 42; in x"#
    );
    // Just verify no panic — result doesn't matter
    let _ = check_str(&src);
}

#[hegel::test(test_cases = 100)]
fn field_access_crash_freedom(tc: TestCase) {
    let field = tc.draw(generators::sampled_from(vec!["x", "y", "nonexistent"]));
    let src = format!(
        r#"/** type T = {{ x: int, y: string }}; */
        let /** type: v :: T.{field} */ v = 42; in v"#
    );
    let _ = check_str(&src);
}

// ==============================================================================
// PBT: resolve_export_typeof removes all TypeOf nodes
// ==============================================================================

/// A ParsedTy leaf that may or may not be a TypeOf.
fn leaf_with_typeof(tc: &TestCase) -> (ParsedTy, Option<SmolStr>) {
    match tc.draw(generators::integers::<u8>().max_value(3)) {
        0 => (ParsedTy::Primitive(PrimitiveTy::Int), None),
        1 => (ParsedTy::Primitive(PrimitiveTy::String), None),
        2 => (ParsedTy::Primitive(PrimitiveTy::Bool), None),
        _ => {
            let i = tc.draw(generators::integers::<u8>().max_value(4));
            let name = SmolStr::from(format!("var{i}"));
            (ParsedTy::TypeOf(name.clone()), Some(name))
        }
    }
}

/// An attrset ParsedTy with 1-3 fields, some of which may be TypeOf.
fn attrset_with_typeof(tc: &TestCase) -> (ParsedTy, Vec<SmolStr>) {
    let keys: Vec<String> = tc.draw(
        generators::vecs(generators::from_regex("[a-z]{1,4}"))
            .min_size(1)
            .max_size(3)
            .unique(true),
    );
    let mut fields = std::collections::BTreeMap::new();
    let mut typeof_names = Vec::new();
    for field_key in keys {
        let (ty, maybe_name) = leaf_with_typeof(tc);
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
}

/// After resolve_export_typeof, the result must contain zero TypeOf nodes.
#[hegel::test(test_cases = 100)]
fn resolve_typeof_removes_all_typeof(tc: TestCase) {
    let (body, typeof_names) = attrset_with_typeof(&tc);
    let export_name: String = tc.draw(generators::from_regex("[A-Z][a-z]{2,5}"));
    let mut raw_exports = HashMap::default();
    raw_exports.insert(SmolStr::from(export_name), body);

    // Build binding_types for all typeof targets
    let mut binding_types = HashMap::default();
    for name in &typeof_names {
        let mut arena = TypeArena::new();
        let root = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
        binding_types.insert(name.clone(), OwnedTy::new(Arc::new(arena), root));
    }

    let resolved = crate::resolve_export_typeof(&raw_exports, &binding_types);
    let remaining = crate::find_typeof_targets(&resolved);
    assert!(
        remaining.is_empty(),
        "resolve_export_typeof should remove all TypeOf nodes, but found: {remaining:?}"
    );
}
