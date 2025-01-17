use smol_str::SmolStr;
use std::collections::HashSet;

use super::{
    AttrSetTy, CheckCtx, Constraint, ConstraintCtx, ConstraintKind, InferenceError, Ty, TyId,
    TypeVariableValue,
};

impl CheckCtx<'_> {
    pub(super) fn solve_constraints(
        &mut self,
        constraints: ConstraintCtx,
    ) -> Result<(), InferenceError> {
        // TODO: this really should loop over multiple times
        // we might not be able to solve all constraints from the start
        // so we need to keep looping until we do a loop without doing anything
        for constraint in constraints.constraints {
            self.solve_constraint(constraint)?;
        }

        Ok(())
    }

    fn solve_constraint(&mut self, constraint: Constraint) -> Result<(), InferenceError> {
        let snapshot = self.table.snapshot();

        let res = match constraint.kind {
            ConstraintKind::Eq(lhs, rhs) => self.unify_var(lhs, rhs),
            // ConstraintKind::Eq(lhs, TyRef::Ref(rhs)) => self.unify_var_ty(lhs, rhs),
        };

        match res {
            Ok(_) => {
                self.table.commit(snapshot);
                Ok(())
            }
            Err(e) => {
                self.table.rollback_to(snapshot);
                Err(e)
            }
        }
    }

    fn unify_var_ty(&mut self, lhs: TyId, rhs: Ty<TyId>) -> Result<Ty<TyId>, InferenceError> {
        // let ret = self.unify(var, rhs.clone())?;
        let rhs_id = rhs.clone().intern_ty(self);
        self.unify(lhs, rhs_id)
    }

    // TODO: still having some sadness with only seeing type vars at the end
    // I think two options
    // make sure i never actually store a type var as a known type, when i "want" to, i would just use the table to unify
    // other option is to make my own abstraction ontop of snapshot vec

    fn unify_var(&mut self, lhs: TyId, rhs: TyId) -> Result<Ty<TyId>, InferenceError> {
        let lhs_val = self.table.inlined_probe_value(lhs);
        let rhs_val = self.table.inlined_probe_value(rhs);

        let res = self.unify(lhs, rhs)?;

        let is_ty_var = matches!(res, Ty::TyVar(_));

        match (lhs_val, rhs_val) {
            (TypeVariableValue::Known(_), TypeVariableValue::Known(_)) => {}
            // _ => self.table.union(lhs, rhs),
            (TypeVariableValue::Known(_), TypeVariableValue::Unknown) => {
                self.table.union(lhs, rhs);
                // self.table
                //     .union_value(rhs, TypeVariableValue::Known(res.clone()));
            }
            (TypeVariableValue::Unknown, TypeVariableValue::Known(_)) => {
                self.table.union(lhs, rhs);
                // self.table
                //     .union_value(lhs, TypeVariableValue::Known(res.clone()));
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

    fn unify(&mut self, lhs: TyId, rhs: TyId) -> Result<Ty<TyId>, InferenceError> {
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
                self.unify_var(a, b)?;
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
                self.unify_var(arg1, arg2)?;
                self.unify_var(ret1, ret2)?;
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                }
            }
            // TODO: https://bernsteinbear.com/blog/row-poly/
            (Ty::AttrSet(_), Ty::AttrSet(_)) => {
                let lhs = self.flatten_attr(lhs);
                let rhs = self.flatten_attr(rhs);
                self.unify_attr(lhs, rhs)?;
                todo!()
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

    fn unify_attr(
        &mut self,
        mut lhs: AttrSetTy<TyId>,
        mut rhs: AttrSetTy<TyId>,
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

        let get_missing = |attr: &AttrSetTy<TyId>, key_set: &HashSet<&SmolStr>| {
            let missing_keys = all_keys.difference(key_set).cloned().cloned();
            attr.get_sub_set(missing_keys)
        };

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
            let lhs_missing = get_missing(&lhs, &lhs_keys);

            if let Some(rest) = rhs.rest {
                // let rhs = self.flatten_attr(rest);
                // return self.unify_attr(lhs_missing, rhs);
                let new_rest = self
                    .unify_var_ty(rest, Ty::AttrSet(lhs_missing))?
                    .intern_ty(self);
                rhs.rest = Some(new_rest);
                return Ok(rhs);
            }
            return Err(InferenceError::UnifyEmptyRest(lhs_missing));
        } else if rhs_keys.is_subset(&lhs_keys) {
            // rhs is missing keys the lhs has
            let rhs_missing = get_missing(&rhs, &rhs_keys);

            if let Some(rest) = lhs.rest {
                let new_rest = self
                    .unify_var_ty(rest, Ty::AttrSet(rhs_missing))?
                    .intern_ty(self);
                lhs.rest = Some(new_rest);
                return Ok(lhs);
            }
            return Err(InferenceError::UnifyEmptyRest(rhs_missing));
        }

        // both are missing stuff so need to unify the two
        match (lhs.rest, rhs.rest) {
            (Some(_), Some(_)) => {
                let lhs_missing = get_missing(&lhs, &lhs_keys);
                let rhs_missing = get_missing(&rhs, &rhs_keys);

                let new_rest = self.alloc_ty(None);

                self.unify_var_ty(new_rest, Ty::AttrSet(lhs_missing))?;
                self.unify_var_ty(new_rest, Ty::AttrSet(rhs_missing))?;
                let mut new_attr = lhs.merge(rhs);
                new_attr.rest = Some(new_rest);
                Ok(new_attr)
            }
            _ => Err(InferenceError::InvalidAttrUnion(lhs, rhs)),
        }
    }
}
