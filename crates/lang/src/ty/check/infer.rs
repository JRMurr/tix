use std::collections::{HashMap, HashSet};

use super::{
    CheckCtx, Constraint, ConstraintCtx, InferenceResult, RootConstraintKind, TyId, TySchema,
    collect::Collector,
};
use crate::{
    AttrSetTy, Ty,
    nameres::{DependentGroup, GroupedDefs},
};

type Substitutions = HashMap<u32, TyId>;

impl CheckCtx<'_> {
    pub fn infer_prog(mut self, groups: GroupedDefs) -> InferenceResult {
        let len = self.module.names().len() + self.module.exprs().len();
        for _ in 0..len {
            self.new_ty_var();
        }

        for group in groups {
            self.infer_scc_group(group);
        }

        self.infer_root();

        let mut collector = Collector::new(self);

        collector.finalize_inference()
    }

    fn infer_root(&mut self) {
        let mut constraints = ConstraintCtx::new();
        self.generate_constraints(&mut constraints, self.module.entry_expr);
        self.solve_constraints(constraints)
            .expect("TODO: solve error aka type error");
    }

    fn infer_scc_group(&mut self, group: DependentGroup) {
        let mut constraints = ConstraintCtx::new();

        for def in &group {
            let ty = self.generate_constraints(&mut constraints, def.expr());
            constraints.add(Constraint {
                kind: RootConstraintKind::Eq(self.ty_for_name(def.name()), ty),
                location: def.expr(),
            });
        }

        self.solve_constraints(constraints)
            .expect("TODO: solve error aka type error");

        // TODO: could there be cases where mutually dependent TypeDefs
        // need to be generalized together (ie)?
        // i don't think it will cause invalid programs to type check but might make
        // errors / canonicalized generics look weird
        for def in &group {
            let name_ty = self.ty_for_name(def.name());
            let generalized_val = self.generalize(name_ty);
            self.poly_type_env.insert(def.name(), generalized_val);
        }
    }

    pub fn instantiate(&mut self, scheme: &TySchema) -> TyId {
        let mut substitutions = HashMap::new();
        for &var in &scheme.vars {
            substitutions.insert(var, self.new_ty_var());
        }

        self.instantiate_ty(scheme.ty, &substitutions)
    }

    fn instantiate_ty(&mut self, ty_id: TyId, substitutions: &Substitutions) -> TyId {
        let ty = self.get_ty(ty_id);

        let new_ty = match ty {
            Ty::TyVar(x) => {
                if let Some(&replacement) = substitutions.get(&x) {
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

    fn generalize(&mut self, ty: TyId) -> TySchema {
        let free_vars = self.free_type_vars(ty);
        TySchema {
            vars: free_vars,
            ty,
            constraints: Box::default(), // TODO
        }
    }

    fn free_type_vars(&mut self, ty_id: TyId) -> HashSet<u32> {
        let mut set = HashSet::new();

        let ty = self.get_ty(ty_id);

        match ty {
            Ty::TyVar(x) => {
                set.insert(x);
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
            }
            Ty::Primitive(_) => {}
        }

        set
    }
}
