use proptest::prelude::{
    any, prop, prop_assert_eq, prop_compose, prop_oneof, proptest, Arbitrary, BoxedStrategy, Just,
    ProptestConfig, Strategy,
};

use crate::{ArcTy, BoolBinOp, ExprBinOp, OverloadBinOp, PrimitiveTy};

use super::arb_arc_ty;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    pub depth: u32,
    pub desired_size: u32,
    pub expected_branch_size: u32,
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
