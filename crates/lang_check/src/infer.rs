use std::collections::{HashMap, HashSet};

use comment_parser::parse_and_collect;
use rustc_hash::FxHashMap;

use crate::Intern;

use super::{
    collect::Collector, AttrMergeConstraint, BinOverloadConstraint, CheckCtx, Constraint,
    ConstraintCtx, DeferrableConstraint, DeferrableConstraintKind, FreeVars, InferenceError,
    InferenceResult, RootConstraintKind, SolveError, TyId, TySchema,
};
use lang_ast::nameres::{DependentGroup, GroupedDefs};
use lang_ty::{AttrSetTy, Ty};

type Substitutions = FxHashMap<TyId, TyId>;

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

        // let groups = if groups.is_empty() { todo!() } else { groups };

        for group in groups {
            self.infer_scc_group(group)?;
        }

        self.infer_root()?;

        let mut collector = Collector::new(self);

        Ok(collector.finalize_inference())
    }

    fn infer_root(&mut self) -> Result<(), InferenceError> {
        let mut constraints = ConstraintCtx::new();
        self.generate_constraints(&mut constraints, self.module.entry_expr);

        // TODO: i think its fine to not do anything with the defers here?
        let _ = get_deferred(self.solve_constraints(constraints))?;

        Ok(())
    }

    fn infer_scc_group(&mut self, group: DependentGroup) -> Result<(), InferenceError> {
        let mut constraints = ConstraintCtx::new();

        for def in &group {
            let name_id = def.name();

            // TODO: get global decs
            let decls = self
                .module
                .type_dec_map
                .docs_for_name(name_id)
                .map(|docs| {
                    let parsed: Vec<_> = docs
                        .iter()
                        .flat_map(|doc| parse_and_collect(doc).expect("TODO: No parse error"))
                        .collect();

                    parsed
                })
                .unwrap_or_default();

            let name_str = &self.module[name_id].text;

            let type_annotation = decls.iter().find_map(|decl| {
                if decl.identifier == *name_str {
                    Some(decl.type_expr.clone())
                } else {
                    None
                }
            });

            // dbg!(&type_annotation);

            let ty_id = if let Some(known_ty) = type_annotation {
                let schema = self.intern_known_ty(name_id, known_ty);

                // TODO: it might be better to have a special constraint
                // for eq a schema to avoid instantiate but its probably fine
                self.instantiate(&schema, &mut constraints)
            } else {
                self.ty_for_name_no_instantiate(name_id)
            };

            let ty = self.generate_constraints(&mut constraints, def.expr());

            constraints.add(Constraint {
                kind: RootConstraintKind::Eq(ty_id, ty),
                location: def.expr(),
            });
        }

        // dbg!(&self.table);
        let deferred_constraints = get_deferred(self.solve_constraints(constraints))?;

        // TODO: could there be cases where mutually dependent TypeDefs
        // need to be generalized together (ie)?
        // i don't think it will cause invalid programs to type check but might make
        // errors / canonicalized generics look weird
        for def in &group {
            let name_id = def.name();
            if self.poly_type_env.contains_key(&name_id) {
                // had a type manual type def
                continue;
            }

            let name_ty = self.ty_for_name_no_instantiate(def.name());
            let generalized_val = self.generalize(name_ty, &deferred_constraints);
            self.poly_type_env.insert(def.name(), generalized_val);
        }
        // TODO: should we assert that all deferred_constraints went somewhere?

        Ok(())
    }

    pub fn instantiate(&mut self, scheme: &TySchema, constraints: &mut ConstraintCtx) -> TyId {
        let mut substitutions = HashMap::default();
        for &var in &scheme.vars {
            substitutions.insert(var, self.new_ty_var());
        }

        // dbg!(&self.table);
        // dbg!(&scheme);

        // TODO: might want to make constraints snapshotable
        for constraint in &scheme.constraints {
            self.instantiate_constraint(constraint, &substitutions, constraints);
        }

        self.instantiate_ty(scheme.ty, &substitutions)
    }

    pub fn instantiate_constraint(
        &mut self,
        overload_constraint: &DeferrableConstraint,
        substitutions: &Substitutions,
        constraints: &mut ConstraintCtx,
    ) {
        let mut get_sub = |ty_id| {
            let ty_id = self.table.find(ty_id);
            let ty = self.get_ty(ty_id);
            if matches!(ty, Ty::TyVar(_)) {
                if let Some(&replacement) = substitutions.get(&ty_id) {
                    return replacement;
                }
                panic!("No substitution found for {ty_id:?}")
            }

            ty_id
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
        // TODO: table.find is not inlined which could cause slowness
        // doesnt seem to have the inlined value exposed...
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
            Ty::Union(inner) => {
                let new_children = inner
                    .iter()
                    .map(|v| self.instantiate_ty(*v, substitutions))
                    .collect();

                Ty::Union(new_children)
            }
        };

        new_ty.intern(self)
    }

    fn generalize(&mut self, ty: TyId, deferred: &DeferredConstraints) -> TySchema {
        let (ty, _) = self.table.flatten(ty);
        let mut free_vars = self.free_type_vars(ty);

        // let to_root = |ty_id| {}

        let mut constraints = Vec::new();

        // TODO: this will always track the deferred constraints if they have any free vars in there
        // which should basically always be true since they are deferred
        // in most cases this is probably fine but might lead to some
        // dupe constraints when things are mutually dependent

        for constraint in deferred {
            let all_vars = constraint.kind.get_vars();
            let maybe_free_vars = all_vars
                .iter()
                .map(|ty_id| self.free_type_vars(*ty_id))
                // TODO: this is probably doing more work than it should
                // could manually create a new hash set
                .reduce(|acc, x| {
                    let res: HashSet<TyId> = acc.union(&x).cloned().collect();
                    res
                })
                .unwrap_or_default();
            if !maybe_free_vars.is_empty() {
                free_vars = free_vars.union(&maybe_free_vars).cloned().collect();
                constraints.push(constraint.clone());
            }
        }

        TySchema {
            vars: free_vars,
            ty,
            constraints: constraints.into(),
        }
    }

    fn free_type_vars(&mut self, ty_id: TyId) -> FreeVars {
        let mut seen = HashSet::new();

        let res = Ty::free_vars_by_ref(ty_id, &mut |id| {
            let id = self.table.find(*id);

            if seen.contains(&id) {
                return None;
            }

            seen.insert(id);

            Some(self.get_ty(id))
        });

        res.iter().map(|id| self.table.find(id.into())).collect()
    }
}
