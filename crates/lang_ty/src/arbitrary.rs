//! Legacy proptest strategies over [`crate::raw_ty`]. Scheduled for removal
//! once `lang_check/src/pbt` is fully on hegel.

use proptest::{
    prelude::{any, prop, prop_oneof, Arbitrary, BoxedStrategy, Just, Strategy},
    prop_compose,
};
use smol_str::SmolStr;

pub use crate::raw_ty::*;
use crate::{PrimitiveTy, TyRef, TypeArena};

/// A generated type with its owning arena. Used by PBT.
#[derive(Debug, Clone)]
pub struct ArbitraryType {
    pub arena: TypeArena,
    pub root: TyRef,
}

pub fn arb_raw_ty(args: RecursiveParams) -> impl Strategy<Value = RawTy> {
    let leaf = prop_oneof![
        8 => any::<PrimitiveTy>().prop_map(RawTy::Primitive),
        1 => (1..=8u32).prop_map(RawTy::TyVar),
        1 => Just(RawTy::Top),
        1 => Just(RawTy::Bottom),
    ];

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            let inner_boxed = inner.clone().prop_map(Box::new);

            prop_oneof![
                3 => inner_boxed.clone().prop_map(RawTy::List),
                3 => (inner_boxed.clone(), inner_boxed.clone())
                    .prop_map(|(param, body)| RawTy::Lambda { param, body }),
                3 => prop::collection::btree_map(arb_smol_str_ident(), inner.clone(), 0..5)
                    .prop_map(RawTy::AttrSet),
                2 => prop::collection::vec(inner.clone(), 2..5).prop_map(RawTy::Union),
                2 => prop::collection::vec(inner.clone(), 2..5).prop_map(RawTy::Intersection),
                1 => inner_boxed.clone().prop_map(RawTy::Neg),
                1 => (arb_smol_str_ident(), inner_boxed.clone())
                    .prop_map(|(name, t)| RawTy::Named(name, t)),
            ]
        },
    )
}

prop_compose! {
    pub fn arb_smol_str_ident()(string in "_pbt_([a-z]|[A-Z]|[0-9]|_){1,10}") -> SmolStr {
        string.into()
    }
}

impl Arbitrary for ArbitraryType {
    type Parameters = RecursiveParams;
    type Strategy = BoxedStrategy<ArbitraryType>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        arb_raw_ty(args)
            .prop_map(|raw| {
                let mut arena = TypeArena::new();
                let root = intern_raw(&mut arena, &raw);
                ArbitraryType { arena, root }
            })
            .boxed()
    }
}

pub fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
    prop_oneof![
        Just(PrimitiveTy::Null),
        Just(PrimitiveTy::Bool),
        Just(PrimitiveTy::Int),
        Just(PrimitiveTy::Float),
        Just(PrimitiveTy::String),
    ]
    .boxed()
}

impl Arbitrary for PrimitiveTy {
    type Parameters = ();
    type Strategy = BoxedStrategy<PrimitiveTy>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_prim().boxed()
    }
}
