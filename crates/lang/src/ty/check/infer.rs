use std::collections::{HashMap, HashSet};

use super::{
    AttrMergeConstraint, BinOverloadConstraint, CheckCtx, Constraint, ConstraintCtx,
    DeferrableConstraint, DeferrableConstraintKind, FreeVars, InferenceError, InferenceResult,
    RootConstraintKind, SolveError, Substitutions, TyId, TySchema, collect::Collector,
};
use crate::{
    AttrSetTy, Ty,
    nameres::{DependentGroup, GroupedDefs},
};

type DeferredConstraints = Vec<DeferrableConstraint>;

fn get_deferred(result: Result<(), SolveError>) -> Result<DeferredConstraints, InferenceError> {
    match result {
        Ok(_) => Ok(Vec::new()),
        Err(e) => match e.deferrable() {
            Some(constraints) => Ok(constraints),
            None => Err(e.inference_error().unwrap()),
        },
    }
}

impl CheckCtx<'_> {
    pub fn infer_prog(mut self, groups: GroupedDefs) -> Result<InferenceResult, InferenceError> {
        let len = self.module.names().len() + self.module.exprs().len();
        for _ in 0..len {
            self.new_ty_var();
        }

        for group in dbg!(groups) {
            self.infer_scc_group(group)?;
        }

        dbg!(&self.table);

        self.infer_root()?;

        let mut collector = Collector::new(self);

        Ok(collector.finalize_inference())
    }

    fn infer_root(&mut self) -> Result<(), InferenceError> {
        println!("INFER ROOT");
        let mut constraints = ConstraintCtx::new();
        self.generate_constraints(&mut constraints, self.module.entry_expr);

        // TODO: i think its fine to not do anything with the defers here?
        let _ = get_deferred(self.solve_constraints(constraints))?;

        Ok(())
    }

    fn infer_scc_group(&mut self, group: DependentGroup) -> Result<(), InferenceError> {
        let mut constraints = ConstraintCtx::new();

        for def in &group {
            let ty = self.generate_constraints(&mut constraints, def.expr());
            constraints.add(Constraint {
                kind: RootConstraintKind::Eq(self.ty_for_name_no_instantiate(def.name()), ty),
                location: def.expr(),
            });
        }

        let deferred_constraints = get_deferred(self.solve_constraints(constraints))?;

        // TODO: could there be cases where mutually dependent TypeDefs
        // need to be generalized together (ie)?
        // i don't think it will cause invalid programs to type check but might make
        // errors / canonicalized generics look weird
        for def in &group {
            let name_ty = self.ty_for_name_no_instantiate(def.name());
            let generalized_val = self.generalize(name_ty, &deferred_constraints);
            self.poly_type_env.insert(def.name(), generalized_val);
        }
        // TODO: should we assert that all deferred_constraints went somewhere?

        Ok(())
    }

    pub fn instantiate(
        &mut self,
        scheme: &TySchema,
        constraints: &mut ConstraintCtx,
    ) -> (TyId, Substitutions) {
        let mut substitutions = HashMap::new();
        for &var in &scheme.vars {
            substitutions.insert(var, self.new_ty_var());
        }

        for constraint in &scheme.constraints {
            self.instantiate_constraint(constraint, &substitutions, constraints);
        }

        // dbg!(scheme);

        let ty = self.instantiate_ty(scheme.ty, &substitutions);

        (ty, substitutions)
    }

    pub fn instantiate_constraint(
        &mut self,
        overload_constraint: &DeferrableConstraint,
        substitutions: &Substitutions,
        constraints: &mut ConstraintCtx,
    ) {
        let get_sub = |ty_id| {
            if let Some(&replacement) = substitutions.get(&ty_id) {
                return replacement;
            }
            panic!("No substitution found for {ty_id:?}")
        };

        let location = overload_constraint.location;
        match &overload_constraint.kind {
            DeferrableConstraintKind::BinOp(bin_op) => {
                constraints.add(Constraint {
                    kind: BinOverloadConstraint {
                        op: bin_op.op,
                        lhs: get_sub(bin_op.lhs),
                        rhs: get_sub(bin_op.rhs),
                        ret_val: get_sub(bin_op.ret_val),
                    }
                    .into(),
                    location,
                });
            }
            DeferrableConstraintKind::Negation(ty_id) => constraints.add(Constraint {
                location,
                kind: DeferrableConstraintKind::Negation(get_sub(*ty_id)).into(),
            }),
            DeferrableConstraintKind::AttrMerge(attr_merge_constraint) => {
                constraints.add(Constraint {
                    kind: AttrMergeConstraint {
                        lhs: get_sub(attr_merge_constraint.lhs),
                        rhs: get_sub(attr_merge_constraint.rhs),
                        ret_val: get_sub(attr_merge_constraint.ret_val),
                    }
                    .into(),
                    location,
                })
            }
        }
    }

    fn instantiate_ty(&mut self, ty_id: TyId, substitutions: &Substitutions) -> TyId {
        // get the root key before replacing
        let ty_id = self.table.find(ty_id);

        let ty = self.get_ty(ty_id);

        let new_ty = match ty {
            Ty::TyVar(x) => {
                if let Some(&replacement) = substitutions.get(&ty_id) {
                    return replacement;
                }
                // this should have been unified by now...
                panic!("No substitution found for Ty::TyVar({x})")
            }
            Ty::Lambda { param, body } => {
                let new_param = self.instantiate_ty(param, substitutions);
                let new_body = self.instantiate_ty(body, substitutions);
                Ty::Lambda {
                    param: new_param,
                    body: new_body,
                }
            }
            Ty::List(inner) => {
                let new_inner = self.instantiate_ty(inner, substitutions);
                Ty::List(new_inner)
            }
            Ty::AttrSet(attr_set_ty) => {
                let new_fields = attr_set_ty
                    .fields
                    .into_iter()
                    .map(|(k, v)| (k, self.instantiate_ty(v, substitutions)))
                    .collect();
                let new_dyn_ty = attr_set_ty
                    .dyn_ty
                    .map(|v| self.instantiate_ty(v, substitutions));

                let new_rest_ty = attr_set_ty
                    .rest
                    .map(|v| self.instantiate_ty(v, substitutions));

                Ty::AttrSet(AttrSetTy {
                    fields: new_fields,
                    dyn_ty: new_dyn_ty,
                    rest: new_rest_ty,
                })
            }
            Ty::Primitive(_) => ty,
        };

        new_ty.intern_ty(self)
    }

    fn generalize(&mut self, ty: TyId, deferred: &DeferredConstraints) -> TySchema {
        let free_vars = self.free_type_vars(ty);

        let constraints = deferred
            .iter()
            .filter(|c| match &c.kind {
                DeferrableConstraintKind::BinOp(bin_overload_constraint) => {
                    bin_overload_constraint.has_free_var(&free_vars)
                }
                DeferrableConstraintKind::Negation(ty_id) => free_vars.contains(ty_id),
                DeferrableConstraintKind::AttrMerge(attr_merge_constraint) => {
                    attr_merge_constraint.has_free_var(&free_vars)
                }
            })
            .cloned()
            .collect();

        TySchema {
            vars: free_vars,
            ty,
            constraints,
        }
    }

    fn free_type_vars(&mut self, ty_id: TyId) -> FreeVars {
        let mut set = HashSet::new();

        // get the root key before getting free vars
        let ty_id = self.table.find(ty_id);

        let ty = self.get_ty(ty_id);

        match ty {
            Ty::TyVar(_) => {
                set.insert(ty_id);
            }
            Ty::List(inner) => set.extend(&self.free_type_vars(inner)),
            Ty::Lambda { param, body } => {
                set.extend(&self.free_type_vars(param));
                set.extend(&self.free_type_vars(body));
            }
            Ty::AttrSet(attr_set_ty) => {
                attr_set_ty.fields.values().for_each(|v| {
                    set.extend(&self.free_type_vars(*v));
                });

                if let Some(dyn_ty) = attr_set_ty.dyn_ty {
                    set.extend(&self.free_type_vars(dyn_ty));
                }

                if let Some(rest_ty) = attr_set_ty.rest {
                    set.extend(&self.free_type_vars(rest_ty));
                }
            }
            Ty::Primitive(_) => {}
        }

        set
    }
}
