use std::collections::{BTreeMap, HashSet};

use lang_ty::{arbitrary::RecursiveParams, ArcTy, PrimitiveTy};
use proptest::prelude::{
    any, prop, prop_assert_eq, prop_compose, prop_oneof, proptest, BoxedStrategy, Just,
    ProptestConfig, Strategy,
};
// use proptest::prelude::*;
use smol_str::SmolStr;

// use crate::{
//     ty::check::tests::get_inferred_root, ArcTy, AttrSetTy, OverloadBinOp, PrimitiveTy, Ty,
// };

fn arb_arc_ty(args: RecursiveParams) -> impl Strategy<Value = ArcTy> {
    let leaf = any::<PrimitiveTy>().prop_map(ArcTy::Primitive);

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            let inner = inner.prop_map(TyRef::from);

            prop_oneof![
                inner.clone().prop_map(ArcTy::List),
                (inner.clone(), inner.clone())
                    .prop_map(|(param, body)| ArcTy::Lambda { param, body }),
                prop::collection::btree_map(arb_smol_str_ident(), inner.clone(), 0..5)
                    .prop_map(|map| ArcTy::AttrSet(AttrSetTy::from_fields(map)))
            ]
        },
    )
}

// TODO: would be nice to make a wrapper type around String to mark at the type level its a nix string
// would make it slightly nicer type safety

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
        prop_oneof![
            Just(format!("(let {ident} = ({val}); in {ident})")),
            Just(format!("(let {ident} = (a: a); in ({ident} ({val})))"))
        ]
    })
}

fn wrap_in_attr(val: NixTextStr) -> impl Strategy<Value = NixTextStr> {
    let key_val_gen = (
        arb_smol_str_ident(),
        any::<PrimitiveTy>().prop_flat_map(prim_ty_to_string),
        // TODO: this might get into recursion hell....
        // ArcTy::arbitrary_with(RecursiveParams {
        //     depth: 2,
        //     desired_size: 4,
        //     expected_branch_size: 2,
        // })
        // .prop_flat_map(|ty| text_from_ty(&ty))
        // .boxed(),
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
        PrimitiveTy::String => arb_str_value().boxed(), // TODO: compose
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
    // Just("".to_string())

    let inner = match ty {
        Ty::TyVar(_) => unreachable!("Nothing should be generating ty vars for now"),
        Ty::Primitive(primitive_ty) => prim_ty_to_string(*primitive_ty).boxed(),
        Ty::List(inner_ref) => {
            let inner = text_from_ty(&inner_ref.0);
            inner.prop_map(|elem| format!("[({elem})]")).boxed()
        }
        Ty::Lambda { param, body } => {
            let body = text_from_ty(&body.0);
            let param = text_from_ty(&param.0);
            (param, body)
                .prop_map(|(param, body)| {
                    format!("(param: let tmp = ({body}); in if param == {param} then tmp else tmp)")
                })
                .boxed()
        }
        Ty::AttrSet(attr_set_ty) => {
            // TODO: merge attr sets
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

                    // escaping is weird, double brace gives one brace in the output
                    format!("({{{}}})", inner)
                })
                .boxed()
        }
    };

    inner.prop_flat_map(non_type_modifying_transform)
    // non_type_modifying_transform(inner).boxed()
}

impl AttrSetTy<TyRef> {
    /// Each child of the attrset for now will be unique
    /// so we need to make sure each child has its own unique ty vars
    fn spread_free_vars(&self, num_free_vars: &mut usize) -> Self {
        // let mut num_free_vars = 0;

        let fields = self
            .fields
            .iter()
            .map(|(k, v)| {
                let free_vars = v.0.free_type_vars();

                let subs: Substitutions = free_vars
                    .iter()
                    .enumerate()
                    .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
                    .collect();

                *num_free_vars += free_vars.len();

                let ty = v.0.normalize_inner(&subs).into();

                (k.clone(), ty)
            })
            .collect();

        // let dyn_ty = self
        //     .dyn_ty
        //     .clone()
        //     .map(|dyn_ty| dyn_ty.0.normalize_inner(free).into());

        // let rest = self
        //     .rest
        //     .clone()
        //     .map(|rest| rest.0.normalize_inner(free).into());

        Self {
            fields,
            dyn_ty: None, // TODO:
            rest: None,   // TODO:
        }
    }
}

impl ArcTy {
    // TODO: make spread_free_vars for all variants
    fn offset_free_vars(&self, num_free_vars: &mut usize) -> Self {
        let free_vars = self.free_type_vars();

        // TODO: extract this
        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
            .collect();

        *num_free_vars += free_vars.len();

        self.normalize_inner(&subs)
    }
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
                // let free_vars_ty = ty.free_type_vars();
                // let free_vars_len = acc_ty.free_type_vars().len();

                // let free_vars_ty: Substitutions = free_vars_ty
                //     .iter()
                //     .enumerate()
                //     .map(|(i, var)| (*var, (free_vars_len + i) as u32))
                //     .collect();

                // let ty = ty.normalize_inner(&free_vars_ty);

                (
                    acc_ty.merge(ty).spread_free_vars(&mut 0),
                    format!("{acc_text} // {text}"),
                )
            })
            .expect("should have at least one elem in the children list for attr merging")
    });

    merged_attrs.prop_map(|(ty, text)| (ArcTy::AttrSet(ty), text))
}

fn func_strat<S: Strategy<Value = (TyRef, NixTextStr)> + Clone>(
    inner: S,
) -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    // format!("(param: let tmp = ({body}); in if param == {param} then tmp else tmp)")
    let fully_known = (inner.clone(), inner.clone()).prop_map(
        |((param_ty, param_text), (body_ty, body_text))| {
            let mut num_free_vars = 0;

            let param_ty = param_ty.0.offset_free_vars(&mut num_free_vars).into();
            let body_ty = body_ty.0.offset_free_vars(&mut num_free_vars).into();

            let ty = ArcTy::Lambda {
                param: param_ty,
                body: body_ty,
            };
            let text = format!(
                "(param: let tmp = ({body_text}); in if param == {param_text} then tmp else tmp)"
            );

            (ty, text)
        },
    );

    let generic = inner.clone().prop_map(|(body_ty, body_text)| {
        let num_free_vars = body_ty.0.free_type_vars().len();

        let param_ty = ArcTy::TyVar((num_free_vars + 1) as u32);

        let ty = ArcTy::Lambda {
            param: param_ty.into(),
            body: body_ty,
        };
        let text = format!("(un_used_param: {body_text})");

        (ty, text)
    });

    prop_oneof![fully_known, generic]
}

fn arb_nix_text(args: RecursiveParams) -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    let leaf = any::<PrimitiveTy>()
        .prop_flat_map(|prim| (Just(ArcTy::Primitive(prim)), prim_ty_to_string(prim)));

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            // TODO: make sure all places where inner is called multiple times
            // does a free var spread
            // TODO: make it automatic?
            let wrapped = inner
                .clone()
                .prop_flat_map(|(ty, text)| (Just(ty), non_type_modifying_transform(text)));

            // all the wrapper types need a ty ref
            let inner = inner.prop_map(|(ty, text)| (TyRef::from(ty), text));

            let list_strat = inner
                .clone() // TODO: gen a list of more than 1 elem
                .prop_map(|(ty, text)| (ArcTy::List(ty), format!("[({text})]")));

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
    any::<ArcTy>().prop_flat_map(|ty| {
        // TODO
        (Just(ty.clone()), text_from_ty(&ty))
    })
}

fn arb_nix() -> impl Strategy<Value = (ArcTy, NixTextStr)> {
    prop_oneof![
        arb_nix_text(RecursiveParams {
            depth: 8,          // 8 levels deep
            desired_size: 256, // Shoot for maximum size of 256 nodes
            expected_branch_size: 3,
        }),
        arb_nix_text_from_ty()
    ]
}

proptest! {
    // default to a smallish value, use the `pbt.sh` script to do more
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]
    #[test]
    fn test_type_check((ty, text) in arb_nix()) {
        let root_ty = get_inferred_root(&text);

        prop_assert_eq!(root_ty, ty.normalize_vars());
    }
}
