mod collect;
mod generate;
mod solve;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use collect::Collector;
use derive_more::Debug;
use ena::unify::{self, InPlaceUnificationTable, UnifyKey, UnifyValue};
use thiserror::Error;

use super::{ArcTy, AttrSetTy, PrimitiveTy, Ty};
use crate::{
    ExprId, Module, NameId,
    db::NixFile,
    nameres::{DependentGroup, GroupedDefs, NameResolution},
};

#[salsa::tracked]
pub fn check_file(db: &dyn crate::Db, file: NixFile) -> InferenceResult {
    let module = crate::module(db, file);

    let name_res = crate::nameres::name_resolution(db, file);

    let grouped_defs = crate::nameres::group_def(db, file);

    let check = CheckCtx::new(&module, &name_res);

    // dbg!(&grouped_defs);

    check.infer_prog(grouped_defs)
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
#[debug("TyId({_0:?})")]
pub struct TyId(u32);

impl From<u32> for TyId {
    #[inline]
    fn from(value: u32) -> Self {
        TyId(value)
    }
}

impl From<usize> for TyId {
    #[inline]
    fn from(value: usize) -> Self {
        (value as u32).into()
    }
}

#[derive(Clone, Debug)]
pub enum TypeVariableValue {
    Known(Ty<TyId>),
    Unknown,
}

impl UnifyKey for TyId {
    type Value = TypeVariableValue;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        TyId(u)
    }

    fn tag() -> &'static str {
        "TyId"
    }
}

impl UnifyValue for TypeVariableValue {
    type Error = unify::NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (value1, value2) {
            // We never equate two type variables, both of which
            // have known types. Instead, we recursively equate
            // those types.
            (&TypeVariableValue::Known { .. }, &TypeVariableValue::Known { .. }) => {
                unreachable!("equating two type variables, both of which have known types")
            }
            // If one side is known, prefer that one.
            (&TypeVariableValue::Known { .. }, &TypeVariableValue::Unknown) => Ok(value1.clone()),
            (&TypeVariableValue::Unknown, &TypeVariableValue::Known { .. }) => Ok(value2.clone()),

            // both unknown, doesn't matter
            (&TypeVariableValue::Unknown, &TypeVariableValue::Unknown) => {
                Ok(TypeVariableValue::Unknown)
            }
        }
    }
}

impl TypeVariableValue {
    /// If this value is known, returns the type it is known to be.
    /// Otherwise, `None`.
    pub(crate) fn known(&self) -> Option<Ty<TyId>> {
        match self {
            TypeVariableValue::Unknown => None,
            TypeVariableValue::Known(value) => Some(value.clone()),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn is_unknown(&self) -> bool {
        match *self {
            TypeVariableValue::Unknown => true,
            TypeVariableValue::Known { .. } => false,
        }
    }
}

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TySchema {
    pub vars: HashSet<u32>, // Each usize corresponds to a Ty::TyVar(x)
    pub ty: TyId,
}

impl Ty<TyId> {
    fn intern_ty(self, ctx: &mut CheckCtx) -> TyId {
        ctx.alloc_ty(Some(self))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint {
    kind: ConstraintKind,
    location: ExprId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintKind {
    Eq(TyId, TyId),
    // Overload()
}

type Substitutions = HashMap<u32, TyId>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintCtx {
    constraints: Vec<Constraint>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    name_ty_map: HashMap<NameId, ArcTy>,
    expr_ty_map: HashMap<ExprId, ArcTy>,
}

impl InferenceResult {
    pub fn ty_for_name(&self, name: NameId) -> ArcTy {
        self.name_ty_map.get(&name).unwrap().clone()
    }

    pub fn ty_for_expr(&self, expr: ExprId) -> ArcTy {
        self.expr_ty_map.get(&expr).unwrap().clone()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
enum InferenceError {
    #[error("Could not union {0:?} and {1:?}")]
    InvalidUnion(Ty<TyId>, Ty<TyId>),

    #[error("Unifying attr set {0:?} with empty ")]
    UnifyEmptyRest(AttrSetTy<TyId>),

    #[error("Could union attr set {0:?} and  {1:?}")]
    InvalidAttrUnion(AttrSetTy<TyId>, AttrSetTy<TyId>),
}

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: InPlaceUnificationTable<TyId>,

    poly_type_env: HashMap<NameId, TySchema>,

    prim_cache: HashMap<PrimitiveTy, TyId>,
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        Self {
            module,
            name_res,
            table: InPlaceUnificationTable::new(),
            poly_type_env: HashMap::new(),
            prim_cache: HashMap::new(),
        }
    }

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
                kind: ConstraintKind::Eq(self.ty_for_name(def.name()), ty),
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

    fn alloc_ty(&mut self, ty: Option<Ty<TyId>>) -> TyId {
        match ty {
            Some(Ty::TyVar(idx)) => {
                let id = TyId(idx);
                self.table.find(id)
            }
            Some(ref ty @ Ty::Primitive(ref prim)) => {
                if let Some(t) = self.prim_cache.get(prim) {
                    *t
                } else {
                    let id = self.table.new_key(TypeVariableValue::Known(ty.clone()));
                    self.prim_cache.insert(prim.clone(), id);
                    id
                }
            }
            Some(ty) => self.table.new_key(TypeVariableValue::Known(ty)),
            None => self.table.new_key(TypeVariableValue::Unknown),
        }
    }

    fn new_ty_var(&mut self) -> TyId {
        self.alloc_ty(None)
    }

    fn ty_for_name(&mut self, name: NameId) -> TyId {
        let ty_schema = self.poly_type_env.get(&name).cloned();

        if let Some(ty_schema) = ty_schema {
            return self.instantiate(&ty_schema);
        }

        // NOTE: this should only happen during the inference of the value for the name
        // after inferring we should add the name to the poly type env
        u32::from(name.into_raw()).into()
    }

    fn ty_for_expr(&self, i: ExprId) -> TyId {
        let idx = self.module.names().len() as u32 + u32::from(i.into_raw());
        idx.into()
    }

    fn get_ty(&mut self, id: TyId) -> Ty<TyId> {
        self.table
            .inlined_probe_value(id)
            .known()
            .unwrap_or(Ty::TyVar(id.0))
    }

    fn instantiate(&mut self, scheme: &TySchema) -> TyId {
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
