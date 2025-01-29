use std::collections::HashSet;

use proptest::prelude::*;
use smol_str::SmolStr;

use crate::{ty::check::tests::get_inferred_root, ArcTy, AttrSetTy, PrimitiveTy, Ty, TyRef};

fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
    prop_oneof![
        Just(PrimitiveTy::Null),
        Just(PrimitiveTy::Bool),
        Just(PrimitiveTy::Int),
        Just(PrimitiveTy::Float),
        Just(PrimitiveTy::String),
        // Just(PrimitiveTy::Path),
        // no uri
    ]
    .boxed()
}

prop_compose! {
    // put a 10 char limit on idents, should be enough....
    fn arb_smol_str_ident()(string in "_pbt_([a-z]|[A-Z]|[0-9]|_){1,10}") -> SmolStr {
        string.into()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    depth: u32,
    desired_size: u32,
    expected_branch_size: u32,
}

impl Default for RecursiveParams {
    fn default() -> Self {
        // TODO: picked basically at random...
        Self {
            depth: 4,                // levels deep
            desired_size: 64,        // total nodes
            expected_branch_size: 5, // items per collection
        }
    }
}

fn arb_arc_ty(args: RecursiveParams) -> impl Strategy<Value = ArcTy> {
    let leaf = arb_prim().prop_map(ArcTy::Primitive);

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

impl Arbitrary for ArcTy {
    type Parameters = RecursiveParams;
    type Strategy = BoxedStrategy<ArcTy>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        arb_arc_ty(args).boxed()
    }
}

// TODO: would be nice to make a wrapper type around String to mark at the type level its a nix string
// would make it slightly nicer type safety

type NixFileStr = String;

fn arb_bool_str() -> impl Strategy<Value = NixFileStr> {
    // let leaf = any::<bool>().prop_map(|b| b.to_string());

    prop_oneof![any::<bool>().prop_map(|b| b.to_string()),]
}

fn arb_int_str() -> impl Strategy<Value = NixFileStr> {
    // let leaf = any::<i32>().prop_map(|i| i.to_string());

    prop_oneof![any::<i32>().prop_map(|i| i.to_string())]
}

prop_compose! {
    fn arb_simple_float()(f in -1.0..2.0) -> f64 {
        f
    }
}


fn arb_float_str() -> impl Strategy<Value = NixFileStr> {
    prop_oneof![arb_simple_float().prop_map(|f| format!("{f:.4}"))]
}

fn arb_str_value() -> impl Strategy<Value = NixFileStr> {
    prop_oneof![arb_smol_str_ident().prop_map(|s| format!("''{s}''"))]
}

fn wrap_in_let(str_gen: impl Strategy<Value = NixFileStr>) -> impl Strategy<Value = NixFileStr> {
    (str_gen, arb_smol_str_ident())
        .prop_map(|(val, ident)| format!("(let {ident} = ({val}); in {ident})"))
}

fn wrap_in_attr(str_gen: impl Strategy<Value = NixFileStr>) -> impl Strategy<Value = NixFileStr> {
    let key_val_gen = (
        arb_smol_str_ident(),
        arb_prim().prop_flat_map(prim_ty_to_string),
        // TODO: this might get into recursion hell....
        // ArcTy::arbitrary_with(RecursiveParams {
        //     depth: 2,
        //     desired_size: 4,
        //     expected_branch_size: 2,
        // })
        // .prop_flat_map(|ty| file_from_ty(&ty))
        // .boxed(),
    );

    let extra_fields = prop::collection::vec(key_val_gen, 0..5);
    let desired_ident = arb_smol_str_ident();

    (extra_fields, desired_ident, str_gen).prop_filter_map(
        "Generated duplicate ident",
        |(mut extra_fields, ident, val)| {
            extra_fields.push((ident.clone(), val));

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

fn prim_ty_to_string(prim: PrimitiveTy) -> impl Strategy<Value = NixFileStr> {
    let leaf: BoxedStrategy<NixFileStr> = match prim {
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

fn file_from_ty(ty: &ArcTy) -> BoxedStrategy<NixFileStr> {
    // Just("".to_string())

    let inner = match ty {
        Ty::TyVar(_) => unreachable!("Nothing should be generating ty vars for now"),
        Ty::Primitive(primitive_ty) => prim_ty_to_string(primitive_ty.clone()).boxed(),
        Ty::List(inner_ref) => {
            let inner = file_from_ty(&inner_ref.0);
            inner.prop_map(|elem| format!("[({elem})]")).boxed()
        }
        Ty::Lambda { param, body } => {
            let body = file_from_ty(&body.0);
            let param = file_from_ty(&param.0);
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
                    let inner = file_from_ty(&val.0);
                    let key = key.clone();
                    inner.prop_map(move |x| format!("\"{key}\"=({x});")).boxed()
                })
                .collect();

            fields
                .prop_map(|fields| {
                    let inner = fields.join(" ");

                    // escaping is weird, double brace gives one brace in the output
                    format!("({{{}}})", inner)
                })
                .boxed()
        }
    };

    prop_oneof![
        inner.clone(),
        wrap_in_let(inner.clone()),
        wrap_in_attr(inner.clone())
    ]
    .boxed()
}

fn arb_nix_file() -> impl Strategy<Value = (ArcTy, String)> {
    any::<ArcTy>().prop_ind_flat_map(|ty| {
        // TODO
        (Just(ty.clone()), file_from_ty(&ty))
    })
}

proptest! {
    // default to a smallish value, use the `pbt.sh` script to do more
    #![proptest_config(ProptestConfig {
        cases: 256, .. ProptestConfig::default()
    })]
    #[test]
    fn test_type_check((ty, file) in arb_nix_file()) {
        let root_ty = get_inferred_root(&file);

        prop_assert_eq!(root_ty, ty);
    }
}
