use proptest::prelude::*;
use smol_str::SmolStr;

use crate::{ArcTy, AttrSetTy, PrimitiveTy, TyRef};

fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
    prop_oneof![
        Just(PrimitiveTy::Null),
        Just(PrimitiveTy::Bool),
        Just(PrimitiveTy::Int),
        Just(PrimitiveTy::Float),
        Just(PrimitiveTy::String),
        Just(PrimitiveTy::Path),
        // no uri
    ]
    .boxed()
}

prop_compose! {
    fn arb_smol_str()(string in any::<String>()) -> SmolStr {
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
                prop::collection::btree_map(arb_smol_str(), inner.clone(), 0..5)
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
