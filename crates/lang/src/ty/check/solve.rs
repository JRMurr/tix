use std::collections::HashSet;

use smol_str::SmolStr;

use super::{
    AttrSetTy, BinOverloadConstraint, CheckCtx, Constraint, ConstraintCtx, ConstraintKind,
    InferenceError, Ty, TyId, TypeVariableValue,
};
use crate::{BinOP, OverloadBinOp, PrimitiveTy};

#[derive(Debug, PartialEq, Eq)]
enum SolveResult {
    Solved,
    Deferred,
    Err(InferenceError),
}

impl From<InferenceError> for SolveResult {
    fn from(value: InferenceError) -> Self {
        SolveResult::Err(value)
    }
}

type UnifyResult = Result<Ty<TyId>, InferenceError>;

impl From<UnifyResult> for SolveResult {
    fn from(value: UnifyResult) -> Self {
        match value {
            Ok(_) => SolveResult::Solved,
            Err(e) => SolveResult::Err(e),
        }
    }
}

impl CheckCtx<'_> {
    pub(super) fn solve_constraints(
        &mut self,
        constraint_ctx: ConstraintCtx,
    ) -> Result<(), InferenceError> {
        let mut made_progress = true;

        let mut constraints = constraint_ctx.constraints;

        while made_progress {
            made_progress = false;

            // We'll collect the constraints that we still can't solve in this pass
            let mut still_unsolved = Vec::new();

            for constraint in constraints {
                match self.solve_constraint(&constraint) {
                    SolveResult::Solved => {
                        // Good—this constraint is done, so we don't put it back in the list.
                        made_progress = true;
                    }
                    SolveResult::Deferred => {
                        // We couldn't solve it yet, let's try again in the next loop
                        still_unsolved.push(constraint);
                    }
                    SolveResult::Err(inference_error) => return Err(inference_error),
                }
            }

            constraints = still_unsolved;
        }

        if !constraints.is_empty() {
            // // We have unsolved constraints but no progress was made.
            // // Possibly ambiguous or underdetermined -> return an error or handle specially
            // return Err(InferenceError::AmbiguousType(...));
            todo!()
        }

        Ok(())
    }

    fn solve_constraint(&mut self, constraint: &Constraint) -> SolveResult {
        let snapshot = self.table.snapshot();

        let res: SolveResult = match &constraint.kind {
            ConstraintKind::Eq(lhs, rhs) => self.unify(*lhs, *rhs).into(),
            ConstraintKind::BinOpOverload(overload_constraint) => {
                self.solve_bin_op(overload_constraint)
            }
            ConstraintKind::NegationOverload(ty) => self.solve_negation(*ty),
        };

        match res {
            SolveResult::Solved => {
                self.table.commit(snapshot);
            }
            _ => {
                self.table.rollback_to(snapshot);
            }
        }

        res
    }

    fn solve_negation(&mut self, ty_id: TyId) -> SolveResult {
        let Some(ty) = self.table.inlined_probe_value(ty_id).known() else {
            return SolveResult::Deferred;
        };

        match ty {
            Ty::Primitive(t) if t.is_number() => SolveResult::Solved,
            _ => SolveResult::Err(InferenceError::InvalidNegation(ty)),
        }
    }

    fn solve_bin_op(&mut self, overload_constraint: &BinOverloadConstraint) -> SolveResult {
        let Some(lhs_val) = self
            .table
            .inlined_probe_value(overload_constraint.lhs)
            .known()
        else {
            return SolveResult::Deferred;
        };
        let Some(rhs_val) = self
            .table
            .inlined_probe_value(overload_constraint.rhs)
            .known()
        else {
            return SolveResult::Deferred;
        };

        let op = overload_constraint.op;

        let Some(ret_ty) = self.solve_bin_op_inner(op, &lhs_val, &rhs_val) else {
            return SolveResult::Err(InferenceError::InvalidBinOp(
                overload_constraint.op,
                lhs_val,
                rhs_val,
            ));
        };

        self.unify_var_ty(overload_constraint.ret_val, ret_ty)
            .into()
    }

    fn solve_bin_op_inner(
        &mut self,
        op: OverloadBinOp,
        lhs: &Ty<TyId>,
        rhs: &Ty<TyId>,
    ) -> Option<Ty<TyId>> {
        use Ty::Primitive;

        // https://nix.dev/manual/nix/2.23/language/operators
        let (Primitive(l), Primitive(r)) = (lhs, rhs) else {
            return None;
        };

        // if both are numbers op doesn't matter
        if l.is_number() && r.is_number() {
            let has_float = l.is_float() || r.is_float();

            let ret_ty = if has_float {
                Primitive(PrimitiveTy::Float)
            } else {
                lhs.clone()
            };

            return Some(ret_ty);
        }

        if !op.is_add() {
            return None;
        }

        // if both are addable (at this point just strings/paths)
        // the return type is the lhs
        if l.is_addable() && r.is_addable() {
            Some(Primitive(l.clone()))
        } else {
            None
        }
    }

    fn unify_var_ty(&mut self, lhs: TyId, rhs: Ty<TyId>) -> UnifyResult {
        // let ret = self.unify(var, rhs.clone())?;
        let rhs_id = rhs.clone().intern_ty(self);
        self.unify(lhs, rhs_id)
    }

    fn unify(&mut self, lhs: TyId, rhs: TyId) -> UnifyResult {
        let lhs_val = self.table.inlined_probe_value(lhs);
        let rhs_val = self.table.inlined_probe_value(rhs);

        let res = self.unify_inner(lhs, rhs)?;

        let is_ty_var = matches!(res, Ty::TyVar(_));

        match (lhs_val, rhs_val) {
            (TypeVariableValue::Known(_), TypeVariableValue::Known(_)) => {}
            // _ => self.table.union(lhs, rhs),
            (TypeVariableValue::Known(_), _) | (_, TypeVariableValue::Known(_)) => {
                self.table.union(lhs, rhs);
                // self.table
                //     .union_value(rhs, TypeVariableValue::Known(res.clone()));
            }
            (TypeVariableValue::Unknown, TypeVariableValue::Unknown) => {
                if !is_ty_var {
                    self.table
                        .union_value(lhs, TypeVariableValue::Known(res.clone()));
                }
                // self.table
                //     .union_value(lhs, TypeVariableValue::Known(res.clone()));
                self.table.union(lhs, rhs);
            }
        }

        Ok(res)
    }

    fn unify_inner(&mut self, lhs: TyId, rhs: TyId) -> UnifyResult {
        if lhs == rhs {
            return Ok(self.get_ty(lhs));
        }

        let ty = match (self.get_ty(lhs), self.get_ty(rhs)) {
            // TODO: Don't think i need a contains in check since how i init the type vars should handle that
            // i things are sad will need to do that and error
            // (Ty::TyVar(a), Ty::TyVar(b)) => {
            //     // self.unify_var(TyId::from(a as u32), TyId::from(b as u32))?;
            //     // Ty::TyVar(a)
            //     return Ok(());
            // }
            (Ty::TyVar(_), other) | (other, Ty::TyVar(_)) => {
                // let id = TyId::from(var as u32);
                // self.unify_var(id, rhs)?;
                other
            }
            (Ty::List(a), Ty::List(b)) => {
                self.unify(a, b)?;
                Ty::List(a)
            }
            (
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                },
                Ty::Lambda {
                    param: arg2,
                    body: ret2,
                },
            ) => {
                self.unify(arg1, arg2)?;
                self.unify(ret1, ret2)?;
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                }
            }
            // TODO: https://bernsteinbear.com/blog/row-poly/
            (Ty::AttrSet(_), Ty::AttrSet(_)) => {
                let lhs = self.flatten_attr(lhs);
                let rhs = self.flatten_attr(rhs);
                Ty::AttrSet(self.unify_attr(lhs, rhs)?)
            }
            (l, r) if l == r => l,
            (l, r) => return Err(InferenceError::InvalidUnion(l, r)),
        };

        Ok(ty)
    }

    fn flatten_attr(&mut self, ty_id: TyId) -> AttrSetTy<TyId> {
        let ty = self.get_ty(ty_id);

        match ty {
            Ty::TyVar(v) => {
                let probed = self.get_ty(v.into());
                if let Ty::TyVar(rest) = probed {
                    return AttrSetTy::from_rest(rest.into());
                }
                unreachable!("Rest type {ty:?} did not resolve to a type variable")
            }
            Ty::AttrSet(attr) => {
                let rest = attr.rest.map(|rest| self.flatten_attr(rest));

                if let Some(rest) = rest {
                    attr.merge(rest)
                } else {
                    attr
                }
            }
            _ => unreachable!("Saw {ty:?} when flattening attr, only expecting TyVar or AttrSet"),
        }
    }

    // TODO: this seems to be returing the right type but its not getting mapped correctly in the
    // final result...
    fn unify_attr(
        &mut self,
        mut lhs: AttrSetTy<TyId>,
        rhs: AttrSetTy<TyId>,
    ) -> Result<AttrSetTy<TyId>, InferenceError> {
        use itertools::Itertools;
        let lhs_keys: HashSet<&SmolStr> = lhs.keys().collect();
        let rhs_keys: HashSet<&SmolStr> = rhs.keys().collect();

        let shared_keys: HashSet<&SmolStr> = lhs_keys.intersection(&rhs_keys).cloned().collect();
        let all_keys: HashSet<&SmolStr> = lhs_keys.union(&rhs_keys).cloned().collect();

        for k in shared_keys.iter().sorted() {
            let lhs_val = lhs.get(k).unwrap();
            let rhs_val = rhs.get(k).unwrap();
            self.unify(*lhs_val, *rhs_val)?;
        }

        // dbg!(&lhs_keys, &rhs_keys, &shared_keys, &all_keys);

        let get_missing = |attr: &AttrSetTy<TyId>, key_set: &HashSet<&SmolStr>| {
            let missing_keys = all_keys.difference(key_set).cloned().cloned();
            attr.get_sub_set(missing_keys)
        };

        let mut lhs_missing = get_missing(&rhs, &lhs_keys);
        let mut rhs_missing = get_missing(&lhs, &rhs_keys);

        if lhs_keys == rhs_keys {
            // both have the same fields, just need to unify the rest
            let rest = match (lhs.rest, rhs.rest) {
                (Some(lhs_rest), Some(rhs_rest)) => {
                    Some(self.unify(lhs_rest, rhs_rest)?.intern_ty(self))
                }
                // both have no rest => done
                (None, None) => None,
                _ => return Err(InferenceError::InvalidAttrUnion(lhs, rhs)),
            };
            lhs.rest = rest;
            return Ok(lhs);
        } else if lhs_keys.is_subset(&rhs_keys) {
            // lhs is missing keys the rhs has
            if let Some(rest) = rhs.rest {
                // let rhs = self.flatten_attr(rest);
                // return self.unify_attr(lhs_missing, rhs);
                // lhs_missing.rest = Some(rest);

                rhs_missing.rest = lhs.rest; // TODO: should this error if lhs has no rest?

                self.unify_var_ty(rest, Ty::AttrSet(rhs_missing))?;

                return Ok(rhs);

                // let new_rest = self
                //     .unify_var_ty(rest, Ty::AttrSet(lhs_missing))?
                //     .intern_ty(self);
                // rhs.rest = Some(new_rest);
                // return Ok(rhs);
            }
            return Err(InferenceError::UnifyEmptyRest(lhs_missing));
        } else if rhs_keys.is_subset(&lhs_keys) {
            // rhs is missing keys the lhs has
            if let Some(rest) = lhs.rest {
                lhs_missing.rest = rhs.rest; // TODO: should this error if rhs has no rest?

                self.unify_var_ty(rest, Ty::AttrSet(lhs_missing))?;

                // let new_rest = self
                //     .unify_var_ty(rest, Ty::AttrSet(rhs_missing))?
                //     .intern_ty(self);
                // lhs.rest = Some(new_rest);
                return Ok(lhs);
            }
            return Err(InferenceError::UnifyEmptyRest(rhs_missing));
        }

        // both are missing stuff so need to unify the two
        match (lhs.rest, rhs.rest) {
            (Some(l_rest), Some(r_rest)) => {
                let new_rest = self.alloc_ty(None);

                lhs_missing.rest = Some(new_rest);
                rhs_missing.rest = Some(new_rest);

                self.unify_var_ty(l_rest, Ty::AttrSet(lhs_missing))?;
                self.unify_var_ty(r_rest, Ty::AttrSet(rhs_missing))?;

                let mut new_attr = lhs.merge(rhs);
                new_attr.rest = Some(new_rest);
                Ok(new_attr)
            }
            _ => Err(InferenceError::InvalidAttrUnion(lhs, rhs)),
        }
    }
}
