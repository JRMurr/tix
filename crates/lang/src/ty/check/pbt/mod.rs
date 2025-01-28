use proptest::prelude::*;
use smol_str::SmolStr;

use crate::{ArcTy, AttrSetTy, PrimitiveTy, Ty, TyRef, ty::check::tests::expect_ty_inference};

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
    fn arb_smol_str_ident()(string in "[a-z]+([a-z]|[A-Z]|[0-9]|_)*") -> SmolStr {
        string.into()
    }
}

fn arb_arc_ty() -> impl Strategy<Value = ArcTy> {
    let leaf = arb_prim().prop_map(ArcTy::Primitive);

    leaf.prop_recursive(
        4,  // 4 levels deep
        64, // 64 total nodes
        5,  // 5 items per collection
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
    type Parameters = ();
    type Strategy = BoxedStrategy<ArcTy>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_arc_ty().boxed()
    }
}

fn prim_ty_to_string(prim: PrimitiveTy) -> BoxedStrategy<String> {
    let inner: BoxedStrategy<String> = match prim {
        PrimitiveTy::Null => Just("null".to_string()).boxed(),
        PrimitiveTy::Bool => any::<bool>().prop_map(|b| b.to_string()).boxed(), // TODO: bool conditions
        PrimitiveTy::Int => any::<i32>().prop_map(|i| i.to_string()).boxed(),   // TODO: ops
        PrimitiveTy::Float => any::<f32>().prop_map(|f| format!("{f:.4}")).boxed(), // TODO: ops
        PrimitiveTy::String => arb_smol_str_ident()
            .prop_map(|s| format!("''{s}''"))
            .boxed(), // TODO: compose
        PrimitiveTy::Path => todo!(),
        PrimitiveTy::Uri => todo!(),
    };

    inner
}

fn file_from_ty(ty: &ArcTy) -> BoxedStrategy<String> {
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

    prop_oneof![inner.clone()]
}

fn arb_nix_file() -> impl Strategy<Value = (ArcTy, String)> {
    arb_arc_ty().prop_ind_flat_map(|ty| {
        // TODO
        (Just(ty.clone()), file_from_ty(&ty))
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 10000, .. ProptestConfig::default()
    })]
    #[test]
    fn test_type_check((ty, file) in arb_nix_file()) {
        expect_ty_inference(&file, ty)
    }
}
