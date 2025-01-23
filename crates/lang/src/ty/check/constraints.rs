use super::TyId;
use crate::{ExprId, OverloadBinOp};

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::RootConstraintKind {}
    impl Sealed for super::OverloadConstraintKind {}
}

pub trait IsConstraintKind: sealed::Sealed {}

// Re-export the sealed implementations.
impl IsConstraintKind for RootConstraintKind {}
impl IsConstraintKind for OverloadConstraintKind {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint<Kind: IsConstraintKind + Clone> {
    pub(crate) kind: Kind,
    pub(crate) location: ExprId,
}

pub type RootConstraint = Constraint<RootConstraintKind>;

pub type OverloadConstraint = Constraint<OverloadConstraintKind>;

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum RootConstraintKind {
    Eq(TyId, TyId),
    Overload(OverloadConstraintKind),
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum OverloadConstraintKind {
    BinOp(BinOverloadConstraint),
    Negation(TyId),
}

impl From<OverloadConstraintKind> for RootConstraintKind {
    fn from(value: OverloadConstraintKind) -> Self {
        RootConstraintKind::Overload(value)
    }
}

impl From<BinOverloadConstraint> for OverloadConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        OverloadConstraintKind::BinOp(value)
    }
}

impl From<BinOverloadConstraint> for RootConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        RootConstraintKind::Overload(OverloadConstraintKind::BinOp(value))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BinOverloadConstraint {
    pub(crate) op: OverloadBinOp,
    pub(crate) lhs: TyId,
    pub(crate) rhs: TyId,
    pub(crate) ret_val: TyId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintCtx {
    pub(crate) constraints: Vec<RootConstraint>,
}

impl ConstraintCtx {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    pub fn add(&mut self, c: RootConstraint) {
        self.constraints.push(c);
    }

    pub fn unify_var(&mut self, e: ExprId, lhs: TyId, rhs: TyId) {
        self.constraints.push(RootConstraint {
            location: e,
            kind: RootConstraintKind::Eq(lhs, rhs),
        });
    }
}
