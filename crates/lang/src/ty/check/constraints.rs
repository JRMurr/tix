use super::TyId;
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
    AttrMerge(AttrMergeConstraint),
}

impl DeferrableConstraintKind {
    pub fn get_vars(&self) -> Vec<TyId> {
        match self {
            DeferrableConstraintKind::BinOp(bin_op) => {
                [bin_op.lhs, bin_op.rhs, bin_op.ret_val].into()
            }
            DeferrableConstraintKind::Negation(ty_id) => [*ty_id].into(),
            DeferrableConstraintKind::AttrMerge(attr_merge) => {
                [attr_merge.lhs, attr_merge.rhs, attr_merge.ret_val].into()
            }
        }
    }
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AttrMergeConstraint {
    pub(crate) lhs: TyId,
    pub(crate) rhs: TyId,
    pub(crate) ret_val: TyId,
}

impl From<AttrMergeConstraint> for DeferrableConstraintKind {
    fn from(value: AttrMergeConstraint) -> Self {
        DeferrableConstraintKind::AttrMerge(value)
    }
}

impl From<AttrMergeConstraint> for RootConstraintKind {
    fn from(value: AttrMergeConstraint) -> Self {
        RootConstraintKind::Deferrable(DeferrableConstraintKind::AttrMerge(value))
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
