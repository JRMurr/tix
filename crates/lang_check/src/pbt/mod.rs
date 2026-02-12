use std::collections::{BTreeMap, HashSet};

use lang_ast::{BoolBinOp, OverloadBinOp};
use lang_ty::{
    arbitrary::{arb_smol_str_ident, RecursiveParams},
    ArcTy, AttrSetTy, OutputTy, PrimitiveTy, TyRef,
};
use proptest::prelude::{
    any, prop, prop_assert_eq, prop_compose, prop_oneof, proptest, BoxedStrategy, Just,
    ProptestConfig, Strategy,
};
use smol_str::SmolStr;

use crate::tests::get_inferred_root;

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

fn text_from_ty(ty: &ArcTy) -> impl Strategy<Value = NixTextStr> {
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
    };

    inner.prop_flat_map(non_type_modifying_transform)
}

fn attr_strat(
    inner: impl Strategy<Value = (TyRef, NixTextStr)>,
) -> impl Strategy<Value = (ArcTy, NixTextStr)> {
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
        PrimitiveTy::Path | PrimitiveTy::Uri => unreachable!("not in arb_prim"),
    }
}

fn func_strat<S: Strategy<Value = (TyRef, NixTextStr)> + Clone>(
    inner: S,
) -> impl Strategy<Value = (ArcTy, NixTextStr)> {
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

fn arb_nix_text(args: RecursiveParams) -> impl Strategy<Value = (ArcTy, NixTextStr)> {
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

fn arb_nix_text_from_ty() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    any::<ArcTy>()
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
fn arb_primitive() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(OutputTy::Primitive(prim)), prim_ty_to_string(prim)))
        .prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)))
}

/// Lists and attrsets of primitives, including `//` merging.
fn arb_structural() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
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
fn arb_lambda() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
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
fn arb_combined() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    // Weight toward arb_nix_text (always succeeds) since arb_nix_text_from_ty
    // has a high rejection rate — randomly generated ArcTy values often contain
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
