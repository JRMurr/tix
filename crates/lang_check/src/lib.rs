mod collect;
mod constraints;
mod generate;
mod infer;
mod solve;
mod storage;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod pbt;

use comment_parser::{KnownTy, TypeVarValue};
pub(crate) use constraints::*;
use derive_more::Debug;
use lang_ast::{AstDb, ExprId, Module, NameId, NameResolution, NixFile, OverloadBinOp};
use lang_ty::{ArcTy, AttrSetTy, PrimitiveTy, Ty};
use std::collections::{HashMap, HashSet};
use storage::TypeStorage;
use thiserror::Error;

#[salsa::tracked]
pub fn check_file(db: &dyn AstDb, file: NixFile) -> Result<InferenceResult, InferenceError> {
    let module = lang_ast::module(db, file);

    let name_res = lang_ast::name_resolution(db, file);

    let grouped_defs = lang_ast::group_def(db, file);

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

impl From<&u32> for TyId {
    #[inline]
    fn from(value: &u32) -> Self {
        TyId(*value)
    }
}

impl From<usize> for TyId {
    #[inline]
    fn from(value: usize) -> Self {
        (value as u32).into()
    }
}

impl From<TyId> for usize {
    #[inline]
    fn from(value: TyId) -> Self {
        value.0 as usize
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

pub trait Intern {
    fn intern(self, ctx: &mut CheckCtx) -> TyId;
}

impl Intern for Ty<TyId> {
    fn intern(self, ctx: &mut CheckCtx) -> TyId {
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
    #[error("Could not unify {0:?} and {1:?}")]
    InvalidUnification(Ty<TyId>, Ty<TyId>),

    #[error("Unifying attr set {0:?} with empty ")]
    UnifyEmptyRest(AttrSetTy<TyId>),

    #[error("Could not unify attr set {0:?} and {1:?}")]
    InvalidAttrUnification(AttrSetTy<TyId>, AttrSetTy<TyId>),

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

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: TypeStorage,

    poly_type_env: HashMap<NameId, TySchema>,

    prim_cache: HashMap<PrimitiveTy, TyId>,
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        Self {
            module,
            name_res,
            table: TypeStorage::new(),
            poly_type_env: HashMap::new(),
            prim_cache: HashMap::new(),
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
                    let id = self.table.insert(ty.clone());
                    self.prim_cache.insert(*prim, id);
                    id
                }
            }
            Some(ty) => self.table.insert(ty),
            None => self.table.new_ty(),
        }
    }

    fn intern_known_ty(&mut self, name: NameId, ty: KnownTy) -> TySchema {
        let free_vars = ty.free_vars(&mut |known_ref| known_ref.0.as_ref().clone());

        let subs: HashMap<TypeVarValue, TyId> = free_vars
            .iter()
            .map(|var| {
                let ty_id = match var {
                    TypeVarValue::Generic(_) => self.new_ty_var(),
                    TypeVarValue::Reference(name) => todo!("Handle reference sub for {name}"),
                };
                (var.clone(), ty_id)
            })
            .collect();

        let ty = self.intern_know_ty_inner(&ty, &subs);

        let schema = TySchema {
            vars: subs.values().cloned().collect(),
            ty,
            constraints: Box::new([]),
        };

        self.poly_type_env.insert(name, schema.clone());
        schema
    }

    // TODO: this is very similar logic to instantiate
    fn intern_know_ty_inner(
        &mut self,
        ty: &KnownTy,
        substitutions: &HashMap<TypeVarValue, TyId>,
    ) -> TyId {
        let ty: Ty<TyId> = match ty {
            Ty::TyVar(var) => {
                let replacement = substitutions
                    .get(var)
                    .unwrap_or_else(|| panic!("No replacement for {var:?}"));
                Ty::TyVar(replacement.0)
            }
            Ty::Primitive(primitive_ty) => Ty::Primitive(*primitive_ty),
            Ty::List(inner) => {
                let new_inner = self.intern_know_ty_inner(&inner.0, substitutions);
                Ty::List(new_inner)
            }
            Ty::Lambda { param, body } => {
                let new_param = self.intern_know_ty_inner(&param.0, substitutions);
                let new_body = self.intern_know_ty_inner(&body.0, substitutions);
                Ty::Lambda {
                    param: new_param,
                    body: new_body,
                }
            }
            Ty::AttrSet(_attr_set_ty) => todo!(),
        };

        ty.intern(self)
    }

    fn new_ty_var(&mut self) -> TyId {
        self.alloc_ty(None)
    }

    fn ty_for_name(&mut self, name: NameId, constraints: &mut ConstraintCtx) -> TyId {
        let ty_schema = self.poly_type_env.get(&name).cloned();

        if let Some(ty_schema) = ty_schema {
            return self.instantiate(&ty_schema, constraints);
        }

        // NOTE: this should only happen during the inference of the value for the name
        // after inferring we should add the name to the poly type env
        u32::from(name.into_raw()).into()
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
            .get(id)
            // .known()
            .unwrap_or(Ty::TyVar(id.0))
    }
}
