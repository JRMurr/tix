use crate::{ArcTy, AttrSetTy, PrimitiveTy, TyRef};
use lang_ast::{BoolBinOp, ExprBinOp, OverloadBinOp};
use proptest::{
    prelude::{any, prop, prop_oneof, Arbitrary, BoxedStrategy, Just, Strategy},
    prop_compose,
};
use smol_str::SmolStr;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    pub depth: u32,
    pub desired_size: u32,
    pub expected_branch_size: u32,
}

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

prop_compose! {
    // put a 10 char limit on identifiers, should be enough....
    fn arb_smol_str_ident()(string in "_pbt_([a-z]|[A-Z]|[0-9]|_){1,10}") -> SmolStr {
        string.into()
    }
}

impl Default for RecursiveParams {
    fn default() -> Self {
        // TODO: picked basically at random...
        Self {
            depth: 4,                // levels deep
            desired_size: 64,        // total nodes
            expected_branch_size: 3, // items per collection
        }
    }
}

impl Arbitrary for ArcTy {
    type Parameters = RecursiveParams;
    type Strategy = BoxedStrategy<ArcTy>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        arb_arc_ty(args).boxed()
    }
}

pub fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
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

impl Arbitrary for PrimitiveTy {
    type Parameters = ();
    type Strategy = BoxedStrategy<PrimitiveTy>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_prim().boxed()
    }
}

impl Arbitrary for OverloadBinOp {
    type Parameters = ();
    type Strategy = BoxedStrategy<OverloadBinOp>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(OverloadBinOp::Add),
            Just(OverloadBinOp::Sub),
            Just(OverloadBinOp::Mul),
            Just(OverloadBinOp::Div),
        ]
        .boxed()
    }
}

impl Arbitrary for BoolBinOp {
    type Parameters = ();
    type Strategy = BoxedStrategy<BoolBinOp>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(BoolBinOp::And),
            Just(BoolBinOp::Implication),
            Just(BoolBinOp::Or),
        ]
        .boxed()
    }
}

impl Arbitrary for ExprBinOp {
    type Parameters = ();
    type Strategy = BoxedStrategy<ExprBinOp>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(ExprBinOp::Less),
            Just(ExprBinOp::LessOrEq),
            Just(ExprBinOp::More),
            Just(ExprBinOp::MoreOrEq),
            Just(ExprBinOp::NotEqual),
            Just(ExprBinOp::Equal),
        ]
        .boxed()
    }
}
