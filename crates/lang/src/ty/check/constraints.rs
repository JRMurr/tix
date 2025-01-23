use super::TyId;
use crate::{ExprId, OverloadBinOp};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint {
    pub(crate) kind: ConstraintKind,
    pub(crate) location: ExprId,
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum ConstraintKind {
    Eq(TyId, TyId),
    Overload(OverloadConstraintKind),
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum OverloadConstraintKind {
    BinOp(BinOverloadConstraint),
    Negation(TyId),
}

impl From<OverloadConstraintKind> for ConstraintKind {
    fn from(value: OverloadConstraintKind) -> Self {
        ConstraintKind::Overload(value)
    }
}

impl From<BinOverloadConstraint> for OverloadConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        OverloadConstraintKind::BinOp(value)
    }
}

impl From<BinOverloadConstraint> for ConstraintKind {
    fn from(value: BinOverloadConstraint) -> Self {
        ConstraintKind::Overload(OverloadConstraintKind::BinOp(value))
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
    pub(crate) constraints: Vec<Constraint>,
}

impl ConstraintCtx {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    pub fn add(&mut self, c: Constraint) {
        self.constraints.push(c);
    }

    pub fn unify_var(&mut self, e: ExprId, lhs: TyId, rhs: TyId) {
        self.constraints.push(Constraint {
            location: e,
            kind: ConstraintKind::Eq(lhs, rhs),
        });
    }
}
