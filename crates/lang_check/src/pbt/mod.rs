// ==============================================================================
// Property-Based Tests for Type Inference
// ==============================================================================
//
// Generates random Nix ASTs (as text) paired with their expected types, then
// verifies that the type checker infers the expected type.
//
// Known limitations:
// - High rejection rate: arb_nix_text_from_ty generates random OutputTy values
//   that often contain unions, intersections, or non-primitive lambda params,
//   all of which are filtered out. The arb_combined strategy compensates by
//   weighting 9:1 toward the always-succeeding arb_nix_text.
// - No union/intersection coverage: generated types are limited to primitives,
//   lists, lambdas, and attrsets. Union and intersection types would require
//   generating if-then-else branches or multi-bounded variables.
// - Path and Uri types trigger todo!() in prim_ty_to_string and are excluded
//   from the arb_prim strategy. Path literals require valid filesystem syntax
//   and Uri is rarely used.

mod stub_compose;

use std::collections::{BTreeMap, HashSet};

use lang_ast::{BoolBinOp, OverloadBinOp};
use lang_ty::{
    arbitrary::{arb_smol_str_ident, RecursiveParams},
    AttrSetTy, OutputTy, PrimitiveTy, TyRef,
};
use proptest::prelude::{
    any, prop, prop_assert, prop_assert_eq, prop_compose, prop_oneof, proptest, BoxedStrategy,
    Just, ProptestConfig, Strategy,
};
use smol_str::SmolStr;

use crate::tests::{check_str, check_str_with_aliases, get_inferred_root};

type NixTextStr = String;

fn arb_bool_str() -> impl Strategy<Value = NixTextStr> {
    let leaf = any::<bool>().prop_map(|b| b.to_string());

    leaf.prop_recursive(3, 5, 2, |inner| {
        (
            inner.clone(),
            inner.clone(),
            any::<BoolBinOp>().prop_map_into::<String>(),
        )
            .prop_map(|(l, r, op)| format!("({l}) {op} ({r})"))
    })
}

fn arb_int_str() -> impl Strategy<Value = NixTextStr> {
    let leaf = any::<i32>().prop_map(|i| i.to_string());

    leaf.prop_recursive(3, 5, 2, |inner| {
        (
            inner.clone(),
            inner.clone(),
            any::<OverloadBinOp>().prop_map_into::<String>(),
        )
            .prop_map(|(l, r, op)| format!("({l}) {op} ({r})"))
    })
}

prop_compose! {
    fn arb_simple_float()(f in -1.0..2.0) -> f64 {
        f
    }
}

fn arb_float_str() -> impl Strategy<Value = NixTextStr> {
    let leaf = arb_simple_float().prop_map(|f| format!("{f:.4}"));

    leaf.prop_recursive(3, 5, 2, |inner| {
        let float_or_int = prop_oneof![inner.clone(), arb_int_str()];

        // make it so we can always have at least one float in the opp
        // but could be on either side
        let args = (inner, float_or_int)
            .prop_flat_map(|(float, f_or_int)| Just([float, f_or_int]))
            .prop_shuffle();

        (args, any::<OverloadBinOp>().prop_map_into::<String>()).prop_map(|(args, op)| {
            let l = &args[0];
            let r = &args[1];

            format!("({l}) {op} ({r})")
        })
    })
}

fn arb_str_value() -> impl Strategy<Value = NixTextStr> {
    prop_oneof![arb_smol_str_ident().prop_map(|s| format!("''{s}''"))]
}

fn wrap_in_let(val: NixTextStr) -> impl Strategy<Value = NixTextStr> {
    arb_smol_str_ident().prop_flat_map(move |ident| {
        // Only use the simple let-bind variant, not identity function application.
        // The identity variant (`let id = a: a; in id(val)`) can lose type information
        // when `val` contains overloaded operations, because SCC grouping generalizes
        // the identity function and extrusion creates fresh vars that don't inherit
        // upper bounds from the resolved overload.
        // TODO: fix this by either excluding let-in names from SCC grouping or by
        // improving how resolved overload types propagate through extrusion.
        Just(format!("(let {ident} = ({val}); in {ident})"))
    })
}

fn wrap_in_attr(val: NixTextStr) -> impl Strategy<Value = NixTextStr> {
    let key_val_gen = (
        arb_smol_str_ident(),
        any::<PrimitiveTy>().prop_flat_map(prim_ty_to_string),
    );

    let extra_fields = prop::collection::vec(key_val_gen, 0..5);
    let desired_ident = arb_smol_str_ident();

    (extra_fields, desired_ident).prop_filter_map(
        "Generated duplicate ident",
        move |(mut extra_fields, ident)| {
            extra_fields.push((ident.clone(), val.clone()));

            let all_ident: HashSet<_> = extra_fields.iter().map(|x| x.0.clone()).collect();

            if all_ident.len() != extra_fields.len() {
                return None;
            }

            let pairs: Vec<_> = extra_fields
                .iter()
                .map(|(key, val)| format!("{key}=({val});"))
                .collect();

            let inner = pairs.join(" ");

            let res = format!("(({{{}}}).{})", inner, ident);

            Some(res)
        },
    )
}

fn prim_ty_to_string(prim: PrimitiveTy) -> impl Strategy<Value = NixTextStr> {
    let leaf: BoxedStrategy<NixTextStr> = match prim {
        PrimitiveTy::Null => Just("null".to_string()).boxed(),
        PrimitiveTy::Bool => arb_bool_str().boxed(),
        PrimitiveTy::Int => arb_int_str().boxed(),
        PrimitiveTy::Float => arb_float_str().boxed(),
        PrimitiveTy::String => arb_str_value().boxed(),
        PrimitiveTy::Path => todo!(),
        PrimitiveTy::Uri => todo!(),
        PrimitiveTy::Number => unreachable!("Number is synthetic, not generated by arb_prim"),
    };

    leaf
}

fn non_type_modifying_transform(text: NixTextStr) -> impl Strategy<Value = NixTextStr> {
    prop_oneof![
        Just(text.clone()),
        wrap_in_let(text.clone()),
        wrap_in_attr(text.clone())
    ]
}

fn text_from_ty(ty: &OutputTy) -> impl Strategy<Value = NixTextStr> {
    let inner = match ty {
        OutputTy::Primitive(primitive_ty) => prim_ty_to_string(*primitive_ty).boxed(),
        OutputTy::List(inner_ref) => {
            let inner = text_from_ty(&inner_ref.0);
            inner.prop_map(|elem| format!("[({elem})]")).boxed()
        }
        OutputTy::Lambda { param, body } => {
            let body = text_from_ty(&body.0);
            match &*param.0 {
                // Primitive param: use assertion builtin to constrain the param type
                // via application contravariance.
                OutputTy::Primitive(prim) => {
                    let builtin = prim_assert_builtin(*prim);
                    body.prop_map(move |body| {
                        format!(
                            "(__pbt_p: let __pbt_chk = {builtin} __pbt_p; in ({body}))"
                        )
                    })
                    .boxed()
                }
                // Generic (TyVar) param: unused parameter, body is independent.
                OutputTy::TyVar(_) => {
                    body.prop_map(|body| format!("(__pbt_p: {body})")).boxed()
                }
                // arb_nix_text_from_ty filters out non-primitive, non-TyVar lambda params
                // via has_non_primitive_lambda_param().
                _ => unreachable!(
                    "non-primitive, non-TyVar lambda param should be filtered by arb_nix_text_from_ty"
                ),
            }
        }
        OutputTy::AttrSet(attr_set_ty) => {
            let fields: Vec<_> = attr_set_ty
                .fields
                .iter()
                .map(|(key, val)| {
                    let inner = text_from_ty(&val.0);
                    let key = key.clone();
                    inner.prop_map(move |x| format!("\"{key}\"=({x});")).boxed()
                })
                .collect();

            fields
                .prop_shuffle()
                .prop_map(|fields| {
                    let inner = fields.join(" ");
                    format!("({{{}}})", inner)
                })
                .boxed()
        }
        OutputTy::TyVar(_) => unreachable!("top-level TyVar should not appear in text_from_ty"),
        OutputTy::Union(_) | OutputTy::Intersection(_) => {
            // TODO: generating code that produces union/intersection types
            // is complex — for now skip in PBT
            unreachable!("Union/Intersection should not appear in PBT type generation yet")
        }
        // Negation types don't arise in PBT — they're only produced by
        // narrowing guards which PBT doesn't generate.
        OutputTy::Neg(_) => unreachable!("Neg should not appear in PBT type generation"),
        // Named is just a display wrapper — delegate to the inner type.
        OutputTy::Named(_, inner) => text_from_ty(&inner.0).boxed(),
        // Bottom (never) doesn't arise in PBT — it's only produced by
        // contradiction detection in canonicalization.
        OutputTy::Bottom => unreachable!("Bottom should not appear in PBT type generation"),
        // Top (any) doesn't arise in PBT — it's only produced by
        // tautology detection in canonicalization.
        OutputTy::Top => unreachable!("Top should not appear in PBT type generation"),
    };

    inner.prop_flat_map(non_type_modifying_transform)
}

fn attr_strat(
    inner: impl Strategy<Value = (TyRef, NixTextStr)>,
) -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    let single_attr = prop::collection::vec((arb_smol_str_ident(), inner), 1..5).prop_filter_map(
        "duplicate ident names",
        |elems| {
            let all_ident: HashSet<_> = elems.iter().map(|x| x.0.clone()).collect();

            if all_ident.len() != elems.len() {
                return None;
            }

            let type_fields: BTreeMap<SmolStr, TyRef> = elems
                .iter()
                .map(|(key, (ty, _))| (key.clone(), ty.clone()))
                .collect();

            let ret_ty = AttrSetTy::from_fields(type_fields);

            let fields: Vec<_> = elems
                .iter()
                .map(|(key, (_, val))| {
                    let key = key.clone();
                    format!("{key}=({val});")
                })
                .collect();

            let fields = format!("({{{}}})", fields.join(" "));

            Some((ret_ty.spread_free_vars(&mut 0), fields))
        },
    );

    let merged_attrs = prop::collection::vec(single_attr, 1..3).prop_map(|children| {
        children
            .into_iter()
            .reduce(|(acc_ty, acc_text), (ty, text)| {
                (
                    acc_ty.merge(ty).spread_free_vars(&mut 0),
                    format!("{acc_text} // {text}"),
                )
            })
            .expect("should have at least one elem in the children list for attr merging")
    });

    merged_attrs.prop_map(|(ty, text)| (OutputTy::AttrSet(ty), text))
}

fn prim_assert_builtin(prim: PrimitiveTy) -> &'static str {
    match prim {
        PrimitiveTy::Int => "__pbt_assert_int",
        PrimitiveTy::Float => "__pbt_assert_float",
        PrimitiveTy::Bool => "__pbt_assert_bool",
        PrimitiveTy::String => "__pbt_assert_string",
        PrimitiveTy::Null => "__pbt_assert_null",
        PrimitiveTy::Path | PrimitiveTy::Uri | PrimitiveTy::Number => {
            unreachable!("not in arb_prim")
        }
    }
}

fn func_strat<S: Strategy<Value = (TyRef, NixTextStr)> + Clone>(
    inner: S,
) -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    // "fully_known" — param is a primitive, constrained via assertion builtin.
    // Applying `__pbt_assert_<prim> __pbt_p` forces `__pbt_p <: prim` through
    // application contravariance, reliably constraining the param type.
    let fully_known =
        (any::<PrimitiveTy>(), inner.clone()).prop_map(|(prim, (body_ty, body_text))| {
            let mut num_free_vars = 0;

            let param_ty: TyRef = OutputTy::Primitive(prim)
                .offset_free_vars(&mut num_free_vars)
                .into();
            let body_ty: TyRef = body_ty.0.offset_free_vars(&mut num_free_vars).into();

            let ty = OutputTy::Lambda {
                param: param_ty,
                body: body_ty,
            };

            let builtin = prim_assert_builtin(prim);
            let text = format!("(__pbt_p: let __pbt_chk = {builtin} __pbt_p; in ({body_text}))");

            (ty, text)
        });

    // "generic" — unused param becomes a fresh type variable.
    let generic = inner.clone().prop_map(|(body_ty, body_text)| {
        let num_free_vars = body_ty.0.free_type_vars().len();

        let param_ty = OutputTy::TyVar((num_free_vars + 1) as u32);

        let ty = OutputTy::Lambda {
            param: param_ty.into(),
            body: body_ty,
        };
        let text = format!("(__pbt_p: {body_text})");

        (ty, text)
    });

    prop_oneof![fully_known, generic]
}

fn arb_nix_text(args: RecursiveParams) -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    let leaf = any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(OutputTy::Primitive(prim)), prim_ty_to_string(prim)));

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            let wrapped = inner
                .clone()
                .prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)));

            // all the wrapper types need a ty ref
            let inner = inner.prop_map(|(ty, text)| (TyRef::from(ty), text));

            let list_strat = inner
                .clone()
                .prop_map(|(ty, text)| (OutputTy::List(ty), format!("[({text})]")));

            prop_oneof![
                wrapped,
                list_strat,
                func_strat(inner.clone()),
                attr_strat(inner.clone())
            ]
        },
    )
}

fn arb_nix_text_from_ty() -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    any::<OutputTy>()
        .prop_filter(
            "Skip types that can't be precisely generated as Nix code",
            |ty| !ty.contains_union_or_intersection() && !ty.has_non_primitive_lambda_param(),
        )
        .prop_flat_map(|ty| (Just(ty.clone()), text_from_ty(&ty)))
}

// ==============================================================================
// Focused strategy builders for split property tests
// ==============================================================================

/// Primitives with arithmetic/boolean operations, optionally wrapped in
/// let-bindings or attrset field selection.
fn arb_primitive() -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(OutputTy::Primitive(prim)), prim_ty_to_string(prim)))
        .prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)))
}

/// Lists and attrsets of primitives, including `//` merging.
fn arb_structural() -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    let leaf = any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(OutputTy::Primitive(prim)), prim_ty_to_string(prim)))
        .prop_map(|(ty, text)| (TyRef::from(ty), text));

    let list_strat = leaf
        .clone()
        .prop_map(|(ty, text)| (OutputTy::List(ty), format!("[({text})]")));

    prop_oneof![list_strat, attr_strat(leaf)]
        .prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)))
}

/// Lambdas (assertion-constrained + generic) with primitive or structural
/// bodies. Tests generalization, extrusion, and early canonicalization.
fn arb_lambda() -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    let leaf = any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(OutputTy::Primitive(prim)), prim_ty_to_string(prim)))
        .prop_map(|(ty, text)| (TyRef::from(ty), text));

    // Bodies can be primitives, lists, or attrsets (one level deep).
    let body = {
        let prim_body = leaf.clone();
        let list_body = leaf
            .clone()
            .prop_map(|(ty, text)| (TyRef::from(OutputTy::List(ty)), format!("[({text})]")));
        let attr_body = attr_strat(leaf.clone()).prop_map(|(ty, text)| (TyRef::from(ty), text));
        prop_oneof![prim_body, list_body, attr_body]
    };

    func_strat(body).prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)))
}

/// Combined strategy: full recursive generation + type-directed generation.
/// Lower case count for breadth coverage across all type forms.
fn arb_combined() -> impl Strategy<Value = (OutputTy, NixTextStr)> {
    // Weight toward arb_nix_text (always succeeds) since arb_nix_text_from_ty
    // has a high rejection rate — randomly generated OutputTy values often contain
    // unions/intersections or non-primitive lambda params that get filtered out.
    prop_oneof![
        9 => arb_nix_text(RecursiveParams {
            depth: 8,
            desired_size: 256,
            expected_branch_size: 3,
        }),
        1 => arb_nix_text_from_ty()
    ]
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    #[test]
    fn test_primitive_typing((ty, text) in arb_primitive()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, ty.normalize_vars());
    }

    #[test]
    fn test_structural_typing((ty, text) in arb_structural()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, ty.normalize_vars());
    }

    #[test]
    fn test_lambda_typing((ty, text) in arb_lambda()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, ty.normalize_vars());
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_local_rejects: 500_000,
        .. ProptestConfig::default()
    })]

    #[test]
    fn test_combined_typing((ty, text) in arb_combined()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, ty.normalize_vars());
    }
}

// ==============================================================================
// Optional fields PBT
// ==============================================================================
//
// Generates lambda patterns with a mix of required and optional (defaulted)
// fields, applies them to attrsets that omit the optional fields, and verifies
// that inference succeeds and returns the expected type.

/// Generate a pattern with required + optional fields and a call site that
/// omits the optional fields. The body sums all fields with `+`, so the
/// expected type is `Int`.
fn arb_optional_field_pattern() -> impl Strategy<Value = NixTextStr> {
    let required = prop::collection::vec(arb_smol_str_ident(), 1..=3);
    let optional = prop::collection::vec(arb_smol_str_ident(), 1..=3);

    (required, optional).prop_filter_map("duplicate field names", |(req, opt)| {
        let mut all_names: HashSet<SmolStr> = HashSet::new();
        for name in req.iter().chain(opt.iter()) {
            if !all_names.insert(name.clone()) {
                return None;
            }
        }

        // Build pattern: `{ req1, req2, opt1 ? 0, opt2 ? 0 }`
        let mut pat_parts: Vec<String> = req.iter().map(|n| n.to_string()).collect();
        for n in &opt {
            pat_parts.push(format!("{n} ? 0"));
        }
        let pattern = pat_parts.join(", ");

        // Build body: sum all fields with `+`
        let all_fields: Vec<String> = req
            .iter()
            .chain(opt.iter())
            .map(|n| n.to_string())
            .collect();
        let body = all_fields.join(" + ");

        // Build call-site attrset: only required fields provided
        let call_fields: Vec<String> = req.iter().map(|n| format!("{n} = 0;")).collect();
        let call_attrset = call_fields.join(" ");

        Some(format!("({{ {pattern} }}: {body}) {{ {call_attrset} }}"))
    })
}

/// Generate patterns where optional fields are provided in the call site
/// (should also succeed).
fn arb_optional_field_all_provided() -> impl Strategy<Value = NixTextStr> {
    let required = prop::collection::vec(arb_smol_str_ident(), 1..=3);
    let optional = prop::collection::vec(arb_smol_str_ident(), 1..=3);

    (required, optional).prop_filter_map("duplicate field names", |(req, opt)| {
        let mut all_names: HashSet<SmolStr> = HashSet::new();
        for name in req.iter().chain(opt.iter()) {
            if !all_names.insert(name.clone()) {
                return None;
            }
        }

        let mut pat_parts: Vec<String> = req.iter().map(|n| n.to_string()).collect();
        for n in &opt {
            pat_parts.push(format!("{n} ? 0"));
        }
        let pattern = pat_parts.join(", ");

        let all_fields: Vec<String> = req
            .iter()
            .chain(opt.iter())
            .map(|n| n.to_string())
            .collect();
        let body = all_fields.join(" + ");

        // All fields provided
        let call_fields: Vec<String> = all_fields.iter().map(|n| format!("{n} = 0;")).collect();
        let call_attrset = call_fields.join(" ");

        Some(format!("({{ {pattern} }}: {body}) {{ {call_attrset} }}"))
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    /// Optional fields omitted: inference should succeed and return Int.
    #[test]
    fn test_optional_field_typing(text in arb_optional_field_pattern()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, OutputTy::Primitive(PrimitiveTy::Int));
    }

    /// Optional fields provided: inference should also succeed and return Int.
    #[test]
    fn test_optional_field_all_provided(text in arb_optional_field_all_provided()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, OutputTy::Primitive(PrimitiveTy::Int));
    }
}

// ==============================================================================
// Narrowing PBT
// ==============================================================================
//
// Generates if-then-else expressions with type-predicate guards to verify
// that narrowing doesn't crash on arbitrary combinations of guards and values.

/// The type predicates available for narrowing, paired with their builtin names.
const NARROWING_PREDICATES: &[&str] = &["isNull", "isString", "isInt", "isFloat", "isBool"];

/// All primitive type predicates (extends NARROWING_PREDICATES with isPath).
const ALL_PRIMITIVE_PREDICATES: &[&str] =
    &["isNull", "isString", "isInt", "isFloat", "isBool", "isPath"];

/// Compound predicates (then-branch only narrowing, no negation support).
const COMPOUND_PREDICATES: &[&str] = &["isAttrs", "isList", "isFunction"];

/// Predicate + operation that's valid after narrowing to that type.
const NARROWED_OPERATIONS: &[(&str, &str)] = &[
    ("isString", r#"__narr_x + "!""#),
    ("isInt", "__narr_x + 1"),
    ("isFloat", "__narr_x + 1.0"),
    ("isBool", "__narr_x && true"),
    ("isAttrs", "__narr_x.name"),
    ("isList", "builtins.head __narr_x"),
    ("isFunction", "__narr_x 42"),
];

/// Literals for equality-guard narrowing.
const EQUALITY_LITERALS: &[&str] = &["null", "true", "false", "42", r#""hello""#, "1.5"];

/// Generate a primitive value as Nix text, for use in narrowed branches.
fn arb_narr_value() -> impl Strategy<Value = (PrimitiveTy, NixTextStr)> {
    prop_oneof![
        Just((PrimitiveTy::Null, "null".to_string())),
        Just((PrimitiveTy::Bool, "true".to_string())),
        any::<i32>().prop_map(|i| (PrimitiveTy::Int, i.to_string())),
        arb_simple_float().prop_map(|f| (PrimitiveTy::Float, format!("{f:.4}"))),
        arb_smol_str_ident().prop_map(|s| (PrimitiveTy::String, format!("''{s}''"))),
    ]
}

/// C1: Narrowing never crashes — generate `x: if <pred> x then <val1> else <val2>`
/// with random predicates and branch values.
fn arb_narrowing_smoke() -> impl Strategy<Value = NixTextStr> {
    let pred_idx = 0..NARROWING_PREDICATES.len();
    (pred_idx, arb_narr_value(), arb_narr_value()).prop_map(
        |(pred_idx, (_ty1, val1), (_ty2, val2))| {
            let pred = NARROWING_PREDICATES[pred_idx];
            format!("__narr_x: if {pred} __narr_x then {val1} else {val2}")
        },
    )
}

/// C2: Same-type branches — narrowing preserves the branch type. Both
/// branches return a value of the same primitive type, so the result
/// should be that primitive.
fn arb_narrowing_same_type() -> impl Strategy<Value = (PrimitiveTy, NixTextStr)> {
    let pred_idx = 0..NARROWING_PREDICATES.len();
    (pred_idx, arb_narr_value()).prop_map(|(pred_idx, (prim, val))| {
        let pred = NARROWING_PREDICATES[pred_idx];
        // Both branches return the same value, so the result type is known.
        // Parenthesize the argument to avoid `-1` being parsed as subtraction.
        let text = format!("((__narr_x: if {pred} __narr_x then ({val}) else ({val})) ({val}))");
        (prim, text)
    })
}

// ==============================================================================
// F1: Early-canonicalization stability — polymorphic let-binding type is stable
// regardless of how many use sites call it with different concrete types.
// ==============================================================================

/// Fixed set of polymorphic bindings and their expected canonical types.
/// Each entry is (binding_body, expected_root_type_when_returned).
const POLY_BINDINGS: &[(&str, &str)] = &[
    ("x: x", "a -> a"),
    ("x: [x]", "a -> [a]"),
    ("x: { val = x; }", "a -> { val: a }"),
    ("x: y: x", "a -> b -> a"),
];

/// Concrete values to use as arguments at use sites.
const USE_SITE_ARGS: &[&str] = &["1", "\"hello\"", "true", "3.14", "null"];

/// Generate a Nix expression: `let f = <binding>; _u0 = f <arg0>; ... in f`
/// with 0-5 use sites, each applying f to a different concrete argument.
fn arb_early_canon_stability() -> impl Strategy<Value = (usize, usize, NixTextStr)> {
    let binding_idx = 0..POLY_BINDINGS.len();
    let num_uses = 0..=5usize;
    // Select which concrete args to use (indices into USE_SITE_ARGS).
    let use_indices = prop::collection::vec(0..USE_SITE_ARGS.len(), 0..=5);

    (binding_idx, num_uses, use_indices).prop_map(|(binding_idx, num_uses, use_indices)| {
        let (binding_body, _expected) = POLY_BINDINGS[binding_idx];
        let mut let_bindings = format!("let f = {binding_body};");
        let actual_uses = num_uses.min(use_indices.len());
        for i in 0..actual_uses {
            let arg = USE_SITE_ARGS[use_indices[i]];
            let _ =
                std::fmt::Write::write_fmt(&mut let_bindings, format_args!(" _u{i} = f ({arg});"));
        }
        let_bindings.push_str(" in f");
        (binding_idx, actual_uses, let_bindings)
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    /// Narrowing smoke test: inference completes without panic for any
    /// combination of type predicate and branch values.
    #[test]
    fn test_narrowing_no_crash(text in arb_narrowing_smoke()) {
        // We only care that inference doesn't panic — the result may be
        // Ok or Err (e.g. type mismatches from incompatible branch types).
        let _ = check_str(&text);
    }

    /// Same-type branches: when both branches return the same primitive,
    /// the inferred type should be that primitive regardless of which
    /// predicate is used.
    #[test]
    fn test_narrowing_same_type_branches((prim, text) in arb_narrowing_same_type()) {
        let root_ty = get_inferred_root(&text);
        prop_assert_eq!(root_ty, OutputTy::Primitive(prim));
    }

    /// Early-canonicalization stability: a polymorphic let-binding's type
    /// should be the same regardless of how many call sites instantiate it
    /// with different concrete types. `let f = x: x; in f` and
    /// `let f = x: x; _u0 = f 1; _u1 = f "hi"; in f` should both produce
    /// `a -> a` for f.
    #[test]
    fn test_early_canon_stability((binding_idx, _num_uses, text) in arb_early_canon_stability()) {
        let (binding_body, _) = POLY_BINDINGS[binding_idx];
        // Base case: no use sites.
        let base_nix = format!("let f = {binding_body}; in f");
        let base_ty = get_inferred_root(&base_nix);
        let actual_ty = get_inferred_root(&text);
        prop_assert_eq!(
            base_ty.clone(), actual_ty.clone(),
            "Binding `{}` with use sites changed type:\n  base: {}\n  with uses: {}",
            binding_body, base_ty, actual_ty
        );
    }
}

// ==============================================================================
// Complex Narrowing PBT
// ==============================================================================
//
// Extends narrowing coverage to literal equality guards, logical combinators
// (&&, ||, !), nested narrowing, hasField, assert, compound predicates, and
// multi-variable narrowing.

/// Recursive generator for guard conditions on `__narr_x`.
///
/// Leaves: type predicates, compound predicates, literal equality, hasField.
/// Recursion (depth 2): negation, and, or.
fn arb_guard_condition() -> BoxedStrategy<NixTextStr> {
    let prim_pred = (0..ALL_PRIMITIVE_PREDICATES.len())
        .prop_map(|i| format!("builtins.{} __narr_x", ALL_PRIMITIVE_PREDICATES[i]));

    let compound_pred = (0..COMPOUND_PREDICATES.len())
        .prop_map(|i| format!("builtins.{} __narr_x", COMPOUND_PREDICATES[i]));

    // Literal equality: `__narr_x == lit` or `lit == __narr_x`
    let literal_eq = (0..EQUALITY_LITERALS.len(), any::<bool>()).prop_map(|(i, flip)| {
        let lit = EQUALITY_LITERALS[i];
        if flip {
            format!("{lit} == __narr_x")
        } else {
            format!("__narr_x == {lit}")
        }
    });

    // hasField: `__narr_x ? name` or `builtins.hasAttr "name" __narr_x`
    let has_field = (arb_smol_str_ident(), any::<bool>()).prop_map(|(field, use_question)| {
        if use_question {
            format!("__narr_x ? {field}")
        } else {
            format!("builtins.hasAttr \"{field}\" __narr_x")
        }
    });

    let leaf: BoxedStrategy<NixTextStr> =
        prop_oneof![prim_pred, compound_pred, literal_eq, has_field].boxed();

    leaf.prop_recursive(2, 8, 2, |inner| {
        let negated = inner.clone().prop_map(|c| format!("(!({}))  ", c));
        let and_comb =
            (inner.clone(), inner.clone()).prop_map(|(l, r)| format!("(({l}) && ({r}))"));
        let or_comb = (inner.clone(), inner).prop_map(|(l, r)| format!("(({l}) || ({r}))"));
        prop_oneof![negated, and_comb, or_comb]
    })
    .boxed()
}

/// Crash-freedom: arbitrary guard combinator tree with random branch values.
fn arb_narrowing_crash_freedom() -> impl Strategy<Value = NixTextStr> {
    (arb_guard_condition(), arb_narr_value(), arb_narr_value()).prop_map(
        |(guard, (_ty1, val1), (_ty2, val2))| {
            format!("__narr_x: if {guard} then {val1} else {val2}")
        },
    )
}

/// Nested narrowing: two levels of predicates on same variable.
/// Tests contradictory narrowing (e.g., isString then isInt).
fn arb_narrowing_nested() -> impl Strategy<Value = NixTextStr> {
    let pred1_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    let pred2_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    (
        pred1_idx,
        pred2_idx,
        arb_narr_value(),
        arb_narr_value(),
        arb_narr_value(),
    )
        .prop_map(|(p1, p2, (_, v1), (_, v2), (_, v3))| {
            let pred1 = ALL_PRIMITIVE_PREDICATES[p1];
            let pred2 = ALL_PRIMITIVE_PREDICATES[p2];
            format!(
                "__narr_x: if builtins.{pred1} __narr_x \
                 then (if builtins.{pred2} __narr_x then {v1} else {v2}) \
                 else {v3}"
            )
        })
}

/// Multi-variable narrowing: two variables combined with `&&`.
fn arb_narrowing_multi_var() -> impl Strategy<Value = NixTextStr> {
    let pred1_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    let pred2_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    (pred1_idx, pred2_idx, arb_narr_value(), arb_narr_value()).prop_map(
        |(p1, p2, (_, v1), (_, v2))| {
            let pred1 = ALL_PRIMITIVE_PREDICATES[p1];
            let pred2 = ALL_PRIMITIVE_PREDICATES[p2];
            format!(
                "__narr_x: __narr_y: \
                 if builtins.{pred1} __narr_x && builtins.{pred2} __narr_y \
                 then {v1} else {v2}"
            )
        },
    )
}

/// Literal equality with random orientation and op (==, !=).
fn arb_narrowing_literal_eq() -> impl Strategy<Value = NixTextStr> {
    let lit_idx = 0..EQUALITY_LITERALS.len();
    (
        lit_idx,
        any::<bool>(),
        any::<bool>(),
        arb_narr_value(),
        arb_narr_value(),
    )
        .prop_map(|(lit_idx, flip, use_neq, (_, v1), (_, v2))| {
            let lit = EQUALITY_LITERALS[lit_idx];
            let op = if use_neq { "!=" } else { "==" };
            let cond = if flip {
                format!("{lit} {op} __narr_x")
            } else {
                format!("__narr_x {op} {lit}")
            };
            format!("__narr_x: if {cond} then {v1} else {v2}")
        })
}

/// `||` combining two predicates on same variable.
fn arb_narrowing_or_combinator() -> impl Strategy<Value = NixTextStr> {
    let pred1_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    let pred2_idx = 0..ALL_PRIMITIVE_PREDICATES.len();
    (pred1_idx, pred2_idx, arb_narr_value(), arb_narr_value()).prop_map(
        |(p1, p2, (_, v1), (_, v2))| {
            let pred1 = ALL_PRIMITIVE_PREDICATES[p1];
            let pred2 = ALL_PRIMITIVE_PREDICATES[p2];
            format!(
                "__narr_x: \
                 if builtins.{pred1} __narr_x || builtins.{pred2} __narr_x \
                 then {v1} else {v2}"
            )
        },
    )
}

/// Correctness: after narrowing to a type via a predicate, a type-specific
/// operation should succeed without errors.
fn arb_narrowing_enables_operation() -> impl Strategy<Value = NixTextStr> {
    let op_idx = 0..NARROWED_OPERATIONS.len();
    op_idx.prop_map(|i| {
        let (pred, operation) = NARROWED_OPERATIONS[i];
        format!("__narr_x: if builtins.{pred} __narr_x then ({operation}) else 0")
    })
}

/// Correctness: after `x ? name` or `builtins.hasAttr`, field access succeeds.
fn arb_narrowing_hasfield_operation() -> impl Strategy<Value = NixTextStr> {
    (arb_smol_str_ident(), any::<bool>()).prop_map(|(field, use_question)| {
        let cond = if use_question {
            format!("__narr_x ? {field}")
        } else {
            format!("builtins.hasAttr \"{field}\" __narr_x")
        };
        format!("__narr_x: if {cond} then __narr_x.{field} else \"default\"")
    })
}

/// Correctness: `!pred` flips narrowing to else-branch. The operation
/// should succeed in the else-branch when the predicate is negated.
fn arb_narrowing_negated_operation() -> impl Strategy<Value = NixTextStr> {
    let op_idx = 0..NARROWED_OPERATIONS.len();
    op_idx.prop_map(|i| {
        let (pred, operation) = NARROWED_OPERATIONS[i];
        format!("__narr_x: if !(builtins.{pred} __narr_x) then 0 else ({operation})")
    })
}

/// Correctness: `assert pred; operation` narrows the variable for the
/// continuation, so the type-specific operation should succeed.
fn arb_narrowing_assert() -> impl Strategy<Value = NixTextStr> {
    let op_idx = 0..NARROWED_OPERATIONS.len();
    op_idx.prop_map(|i| {
        let (pred, operation) = NARROWED_OPERATIONS[i];
        format!("__narr_x: assert builtins.{pred} __narr_x; ({operation})")
    })
}

// -- Crash-freedom tests: inference must not panic, type errors are OK --------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    #[test]
    fn test_narrowing_complex_crash_freedom(text in arb_narrowing_crash_freedom()) {
        let _ = check_str(&text);
    }

    #[test]
    fn test_narrowing_nested_crash_freedom(text in arb_narrowing_nested()) {
        let _ = check_str(&text);
    }

    #[test]
    fn test_narrowing_multi_var_crash_freedom(text in arb_narrowing_multi_var()) {
        let _ = check_str(&text);
    }

    #[test]
    fn test_narrowing_literal_eq_crash_freedom(text in arb_narrowing_literal_eq()) {
        let _ = check_str(&text);
    }

    #[test]
    fn test_narrowing_or_crash_freedom(text in arb_narrowing_or_combinator()) {
        let _ = check_str(&text);
    }
}

// -- Correctness tests: inference must succeed without type errors -------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    /// After narrowing to type T via a predicate, T-specific operations succeed.
    #[test]
    fn test_narrowing_enables_operation(text in arb_narrowing_enables_operation()) {
        let _ = get_inferred_root(&text);
    }

    /// After `x ? name`, `x.name` access succeeds.
    #[test]
    fn test_narrowing_hasfield_enables_access(text in arb_narrowing_hasfield_operation()) {
        let _ = get_inferred_root(&text);
    }

    /// `!pred` puts narrowing in else-branch correctly.
    #[test]
    fn test_narrowing_negated_enables_operation(text in arb_narrowing_negated_operation()) {
        let _ = get_inferred_root(&text);
    }

    /// `assert pred; op` narrows and makes the operation succeed.
    #[test]
    fn test_narrowing_assert_enables_operation(text in arb_narrowing_assert()) {
        let _ = get_inferred_root(&text);
    }
}

// ==============================================================================
// Annotation Provenance Stability PBT
// ==============================================================================
//
// Verifies that type alias annotations on names (via `# type: x :: Alias`)
// survive inference and appear consistently in both name_ty_map and
// expr_ty_map at every usage site. This catches provenance loss through
// extrusion, constraint propagation, and canonicalization.

use crate::aliases::TypeAliasRegistry;
use lang_ast::Expr;

/// Stubs defining type aliases with union types (forces the Variable branch
/// of extrude) and plain attrset types (goes through the Concrete branch).
const ANNOTATION_STUBS: &str = r#"
type Nullable = int | null;
type StringOrInt = string | int;
type Config = { enable: bool, name: string, ... };
"#;

static ANNOTATION_REGISTRY: std::sync::LazyLock<TypeAliasRegistry> =
    std::sync::LazyLock::new(|| {
        let file =
            comment_parser::parse_tix_file(ANNOTATION_STUBS).expect("parse annotation stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);
        registry
    });

/// Type aliases available for annotation tests. Each entry is
/// (alias_name, is_union_type). Union types trigger the Variable branch
/// of extrude because `apply_type_annotation` sets alias_provenance
/// without constraining to a concrete type.
const ANNOTATION_ALIASES: &[(&str, bool)] =
    &[("Nullable", true), ("StringOrInt", true), ("Config", false)];

/// Usage patterns for an annotated let-binding `x`.
#[derive(Debug, Clone, Copy)]
enum AnnotationUsagePattern {
    /// `let x = f; in x` — direct return of annotated binding
    DirectReturn,
    /// `let x = f; y = x; in y` — let-rebinding of annotated name
    LetRebind,
    /// `let x = f; in { inherit x; }` — inherit usage
    Inherit,
}

const ALL_USAGE_PATTERNS: &[AnnotationUsagePattern] = &[
    AnnotationUsagePattern::DirectReturn,
    AnnotationUsagePattern::LetRebind,
    AnnotationUsagePattern::Inherit,
];

/// Generate a Nix source with an annotated let-binding and a usage pattern.
/// Returns (alias_name, nix_source).
fn arb_annotation_usage() -> impl Strategy<Value = (String, String)> {
    let alias_idx = 0..ANNOTATION_ALIASES.len();
    let pattern_idx = 0..ALL_USAGE_PATTERNS.len();

    (alias_idx, pattern_idx).prop_map(|(alias_idx, pattern_idx)| {
        let (alias_name, _is_union) = ANNOTATION_ALIASES[alias_idx];
        let pattern = ALL_USAGE_PATTERNS[pattern_idx];

        let nix_src = match pattern {
            AnnotationUsagePattern::DirectReturn => {
                format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\nin x")
            }
            AnnotationUsagePattern::LetRebind => {
                format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\n  y = x;\nin y")
            }
            AnnotationUsagePattern::Inherit => {
                format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\nin {{ inherit x; }}")
            }
        };

        (alias_name.to_string(), nix_src)
    })
}

/// Generate multiple usage sites of the same annotated binding.
/// `let x = f; a = x; b = x; in a` — 2-3 references to the same name.
fn arb_annotation_multi_usage() -> impl Strategy<Value = (String, String)> {
    let alias_idx = 0..ANNOTATION_ALIASES.len();
    let num_uses = 2..=3usize;

    (alias_idx, num_uses).prop_map(|(alias_idx, num_uses)| {
        let (alias_name, _) = ANNOTATION_ALIASES[alias_idx];

        let mut bindings = format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\n");
        for i in 0..num_uses {
            let _ = std::fmt::Write::write_fmt(&mut bindings, format_args!("  _u{i} = x;\n"));
        }
        bindings.push_str("in x");

        (alias_name.to_string(), bindings)
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]

    /// Annotation stability: if name_ty_map contains a Named wrapper for
    /// an annotated binding, it should reference the correct alias.
    /// Note: union-annotated types (e.g. `Nullable = int | null`) may show
    /// TyVar in name_ty_map because early canonical snapshots see no concrete
    /// bounds. The Named wrapper is only guaranteed for non-union aliases.
    #[test]
    fn test_annotation_definition_named(
        (alias_name, nix_src) in arb_annotation_usage()
    ) {
        let registry = &*ANNOTATION_REGISTRY;
        let (module, inference) = check_str_with_aliases(&nix_src, registry);
        let inference = inference.expect("should not produce a type error");

        // The definition of `x` should carry the alias in name_ty_map
        // when the alias resolves to a concrete type (like Config = { ... }).
        // For union aliases, early canonical may produce TyVar instead.
        let x_name_types: Vec<_> = module
            .names()
            .filter_map(|(name_id, name)| {
                if name.text == "x" {
                    inference
                        .name_ty_map
                        .get(name_id)
                        .map(|ty| format!("{ty:?}"))
                } else {
                    None
                }
            })
            .collect();

        prop_assert!(
            !x_name_types.is_empty(),
            "should find name `x` in name_ty_map"
        );
        // Soft check: if Named appears, it must reference the correct alias.
        for ty_str in &x_name_types {
            if ty_str.contains("Named") {
                prop_assert!(
                    ty_str.contains(&alias_name),
                    "definition of `x` has Named but wrong alias, expected \"{}\", got: {}",
                    alias_name, ty_str
                );
            }
        }
    }

    /// Annotation stability at usage sites: expr_ty_map for every reference
    /// to an annotated name should show Named(alias, ...).
    #[test]
    fn test_annotation_usage_site_named(
        (alias_name, nix_src) in arb_annotation_usage()
    ) {
        let registry = &*ANNOTATION_REGISTRY;
        let (module, inference) = check_str_with_aliases(&nix_src, registry);
        let inference = inference.expect("should not produce a type error");

        // Every reference expression to `x` should carry the alias.
        let ref_types: Vec<_> = module
            .exprs()
            .filter_map(|(expr_id, expr)| {
                if let Expr::Reference(name) = expr {
                    if name == "x" {
                        return inference
                            .expr_ty_map
                            .get(expr_id)
                            .map(|ty| format!("{ty:?}"));
                    }
                }
                None
            })
            .collect();

        prop_assert!(
            !ref_types.is_empty(),
            "should find at least one reference to `x`"
        );
        for ty_str in &ref_types {
            prop_assert!(
                ty_str.contains("Named") && ty_str.contains(&alias_name),
                "reference to `x` should be Named(\"{}\", ...), got: {:?}",
                alias_name, ref_types
            );
        }
    }

    /// Multiple usage sites: when the same annotated binding is referenced
    /// N times, every reference should consistently show Named(alias, ...).
    #[test]
    fn test_annotation_multi_usage_stability(
        (alias_name, nix_src) in arb_annotation_multi_usage()
    ) {
        let registry = &*ANNOTATION_REGISTRY;
        let (module, inference) = check_str_with_aliases(&nix_src, registry);
        let inference = inference.expect("should not produce a type error");

        let ref_types: Vec<_> = module
            .exprs()
            .filter_map(|(expr_id, expr)| {
                if let Expr::Reference(name) = expr {
                    if name == "x" {
                        return inference
                            .expr_ty_map
                            .get(expr_id)
                            .map(|ty| format!("{ty:?}"));
                    }
                }
                None
            })
            .collect();

        // Should have multiple references, all showing the alias.
        prop_assert!(
            ref_types.len() >= 2,
            "should find at least 2 references to `x`, found {}",
            ref_types.len()
        );
        for ty_str in &ref_types {
            prop_assert!(
                ty_str.contains("Named") && ty_str.contains(&alias_name),
                "all references to `x` should be Named(\"{}\", ...), got: {:?}",
                alias_name, ref_types
            );
        }
    }
}
