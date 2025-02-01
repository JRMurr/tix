use proptest::prelude::{prop_oneof, Arbitrary, BoxedStrategy, Just, Strategy};

use crate::{BoolBinOp, ExprBinOp, OverloadBinOp};

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
