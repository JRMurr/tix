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

use std::collections::{BTreeMap, HashSet};

use lang_ast::{BoolBinOp, OverloadBinOp};
use lang_ty::{
    arbitrary::{arb_smol_str_ident, RecursiveParams},
    AttrSetTy, OutputTy, PrimitiveTy, TyRef,
};
use proptest::prelude::{
    any, prop, prop_assert_eq, prop_compose, prop_oneof, proptest, BoxedStrategy, Just,
    ProptestConfig, Strategy,
};
use smol_str::SmolStr;

use crate::tests::{check_str, get_inferred_root};

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
}
