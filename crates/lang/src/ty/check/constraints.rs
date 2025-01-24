use super::{FreeVars, TyId};
use crate::{ExprId, OverloadBinOp};

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::RootConstraintKind {}
    impl Sealed for super::DeferrableConstraintKind {}
}

pub trait IsConstraintKind: sealed::Sealed {}

// Re-export the sealed implementations.
impl IsConstraintKind for RootConstraintKind {}
impl IsConstraintKind for DeferrableConstraintKind {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint<Kind: IsConstraintKind + Clone> {
    pub(crate) kind: Kind,
    pub(crate) location: ExprId,
}

pub type RootConstraint = Constraint<RootConstraintKind>;

impl RootConstraint {
    pub fn overload(&self) -> Option<DeferrableConstraint> {
        match &self.kind {
            RootConstraintKind::Deferrable(o) => Some(DeferrableConstraint {
                kind: o.clone(),
                location: self.location,
            }),
            _ => None,
        }
    }
}

pub type DeferrableConstraint = Constraint<DeferrableConstraintKind>;

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum RootConstraintKind {
    Eq(TyId, TyId),
    Deferrable(DeferrableConstraintKind),
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum DeferrableConstraintKind {
    BinOp(BinOverloadConstraint),
    Negation(TyId),
}

impl From<DeferrableConstraintKind> for RootConstraintKind {
    fn from(value: DeferrableConstraintKind) -> Self {
        RootConstraintKind::Deferrable(value)
    }
}

impl From<BinOverloadConstraint> for DeferrableConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        DeferrableConstraintKind::BinOp(value)
    }
}

impl From<BinOverloadConstraint> for RootConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        RootConstraintKind::Deferrable(DeferrableConstraintKind::BinOp(value))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BinOverloadConstraint {
    pub(crate) op: OverloadBinOp,
    pub(crate) lhs: TyId,
    pub(crate) rhs: TyId,
    pub(crate) ret_val: TyId,
}

impl BinOverloadConstraint {
    // check if either the lhs or rhs is in the free vars
    // TODO: don't think we need to check the ret since it only would be set if the lhs and rhs are known
    pub fn has_free_var(&self, free: &FreeVars) -> bool {
        free.contains(&self.lhs) || free.contains(&self.rhs)
    }
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
