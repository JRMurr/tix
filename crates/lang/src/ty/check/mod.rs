mod collect;
mod constraints;
mod generate;
mod infer;
mod solve;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

pub(crate) use constraints::*;
use derive_more::Debug;
use ena::unify::{self, InPlaceUnificationTable, UnifyKey, UnifyValue};
use thiserror::Error;

use super::{ArcTy, AttrSetTy, PrimitiveTy, Ty};
use crate::{ExprId, Module, NameId, OverloadBinOp, db::NixFile, nameres::NameResolution};

#[salsa::tracked]
pub fn check_file(db: &dyn crate::Db, file: NixFile) -> Result<InferenceResult, InferenceError> {
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

pub type FreeVars = HashSet<TyId>;

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TySchema {
    pub vars: FreeVars,
    pub ty: TyId,
    pub constraints: Box<[DeferrableConstraint]>,
}

impl Ty<TyId> {
    fn intern_ty(self, ctx: &mut CheckCtx) -> TyId {
        ctx.alloc_ty(Some(self))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    pub name_ty_map: HashMap<NameId, ArcTy>,
    pub expr_ty_map: HashMap<ExprId, ArcTy>,
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
pub enum InferenceError {
    #[error("Could not union {0:?} and {1:?}")]
    InvalidUnion(Ty<TyId>, Ty<TyId>),

    #[error("Unifying attr set {0:?} with empty ")]
    UnifyEmptyRest(AttrSetTy<TyId>),

    #[error("Could union attr set {0:?} and  {1:?}")]
    InvalidAttrUnion(AttrSetTy<TyId>, AttrSetTy<TyId>),

    #[error("Can not negate non number type {0:?}")]
    InvalidNegation(Ty<TyId>),

    #[error("Can not do binary operation ({1:?}) ({0:?}) ({2:?})")]
    InvalidBinOp(OverloadBinOp, Ty<TyId>, Ty<TyId>),

    #[error("Can not do attrset merge on ({0:?}) ({1:?})")]
    InvalidAttrMerge(Ty<TyId>, Ty<TyId>),
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SolveError {
    #[error(transparent)]
    InferenceError(#[from] InferenceError),

    #[error("Unsolved constraints {0:?}")]
    UnsolvedConstraints(Box<[RootConstraint]>),
}

impl SolveError {
    /// If the Solve error is only unsolved Overload constraints
    /// it could be solved later by tracking them on the appropriate [TySchema]
    pub fn deferrable(&self) -> Option<Vec<DeferrableConstraint>> {
        let SolveError::UnsolvedConstraints(constraints) = self else {
            return None;
        };

        let num_constrains = constraints.len();

        let overload_constraints: Vec<_> =
            constraints.iter().filter_map(|c| c.overload()).collect();

        if num_constrains == overload_constraints.len() {
            Some(overload_constraints)
        } else {
            None
        }
    }

    pub fn inference_error(self) -> Option<InferenceError> {
        match self {
            SolveError::InferenceError(inference_error) => Some(inference_error),
            SolveError::UnsolvedConstraints(_) => None,
        }
    }
}

pub type Substitutions = HashMap<TyId, TyId>;

#[derive(Debug, Clone, Default)]
pub struct SubstitutionScopes {
    scopes: Vec<Substitutions>,
}

impl SubstitutionScopes {
    pub fn push(&mut self, scope: Substitutions) {
        self.scopes.push(scope);
    }

    pub fn pop(&mut self) -> Option<Substitutions> {
        self.scopes.pop()
    }

    pub fn get_sub(&self, key: &TyId) -> Option<TyId> {
        for scope in self.scopes.iter().rev() {
            if let Some(sub) = dbg!(scope).get(key) {
                return Some(*sub);
            }
        }

        None
    }
}

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: InPlaceUnificationTable<TyId>,

    poly_type_env: HashMap<NameId, TySchema>,

    prim_cache: HashMap<PrimitiveTy, TyId>,

    sub_scopes: SubstitutionScopes,
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        Self {
            module,
            name_res,
            table: InPlaceUnificationTable::new(),
            poly_type_env: HashMap::new(),
            prim_cache: HashMap::new(),
            sub_scopes: SubstitutionScopes::default(),
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

    fn ty_for_name(
        &mut self,
        name: NameId,
        constraints: &mut ConstraintCtx,
    ) -> (TyId, Substitutions) {
        let ty_schema = self.poly_type_env.get(&name).cloned();

        dbg!(name);

        if let Some(ty_schema) = ty_schema {
            return self.instantiate(&ty_schema, constraints);
        }

        // NOTE: this should only happen during the inference of the value for the name
        // after inferring we should add the name to the poly type env
        let ty: TyId = u32::from(name.into_raw()).into();

        (
            dbg!(self.sub_scopes.get_sub(&ty)).unwrap_or(ty),
            HashMap::new(),
        )
    }

    fn ty_for_name_no_subs(&mut self, name: NameId, constraints: &mut ConstraintCtx) -> TyId {
        let (ty, subs) = self.ty_for_name(name, constraints);
        // TODO: this will probably be sad but good for sanity for now
        debug_assert!(subs.is_empty());
        ty
    }

    fn ty_for_name_no_instantiate(&mut self, name: NameId) -> TyId {
        // TODO: not sure if this will always hold but good to check the assumption
        // the only case it would be nice to ignore would be during canonicalizing
        debug_assert!(!self.poly_type_env.contains_key(&name));

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
}
