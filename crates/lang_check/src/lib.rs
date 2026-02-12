mod builtins;
pub(crate) mod collect;
mod constrain;
mod infer;
pub(crate) mod infer_expr;
pub(crate) mod storage;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod pbt;

use comment_parser::{ParsedTy, TypeVarValue};
use derive_more::Debug;
use infer_expr::{PendingMerge, PendingOverload};
use lang_ast::{AstDb, ExprId, Module, NameId, NameResolution, NixFile, OverloadBinOp};
use lang_ty::{ArcTy, OutputTy, PrimitiveTy, Ty};
use std::collections::{HashMap, HashSet};
use storage::TypeStorage;
use thiserror::Error;

#[salsa::tracked]
pub fn check_file(db: &dyn AstDb, file: NixFile) -> Result<InferenceResult, InferenceError> {
    let module = lang_ast::module(db, file);

    let name_res = lang_ast::name_resolution(db, file);

    let grouped_defs = lang_ast::group_def(db, file);

    let check = CheckCtx::new(&module, &name_res);

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
    #[error("Type mismatch: {0:?} is not a subtype of {1:?}")]
    TypeMismatch(Ty<TyId>, Ty<TyId>),

    #[error("Missing field: {0:?}")]
    MissingField(smol_str::SmolStr),

    #[error("Can not negate non number type {0:?}")]
    InvalidNegation(Ty<TyId>),

    #[error("Can not do binary operation ({1:?}) ({0:?}) ({2:?})")]
    InvalidBinOp(OverloadBinOp, Ty<TyId>, Ty<TyId>),

    #[error("Can not do attrset merge on ({0:?}) ({1:?})")]
    InvalidAttrMerge(Ty<TyId>, Ty<TyId>),
}

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: TypeStorage,

    /// Maps generalized names to their polymorphic TyId.
    /// The TyId + variable levels encode the polymorphic scheme.
    poly_type_env: HashMap<NameId, TyId>,

    /// Cache (sub, sup) pairs already processed by constrain() to avoid cycles.
    constrain_cache: HashSet<(TyId, TyId)>,

    /// Primitive type cache for deduplication.
    prim_cache: HashMap<PrimitiveTy, TyId>,

    /// Pending overloaded binary op constraints to resolve later.
    pending_overloads: Vec<PendingOverload>,

    /// Pending attrset merge constraints to resolve later.
    pending_merges: Vec<PendingMerge>,

    /// Overloads that couldn't be resolved in their SCC group and should be
    /// re-instantiated per call-site during extrusion.
    /// Maps from operand TyId → list of deferred overloads referencing that var.
    deferred_overloads: Vec<PendingOverload>,

    /// Early-canonicalized types for names, captured at generalization time
    /// before use-site extrusions contaminate polymorphic variables with
    /// concrete bounds.
    early_canonical: HashMap<NameId, OutputTy>,
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        Self {
            module,
            name_res,
            table: TypeStorage::new(),
            poly_type_env: HashMap::new(),
            constrain_cache: HashSet::new(),
            prim_cache: HashMap::new(),
            pending_overloads: Vec::new(),
            pending_merges: Vec::new(),
            deferred_overloads: Vec::new(),
            early_canonical: HashMap::new(),
        }
    }

    /// Allocate a fresh type variable at the current level.
    fn new_var(&mut self) -> TyId {
        self.table.new_var()
    }

    /// Allocate a concrete type and return its TyId.
    fn alloc_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        self.table.new_concrete(ty)
    }

    /// Allocate a primitive type, deduplicating via cache.
    fn alloc_prim(&mut self, prim: PrimitiveTy) -> TyId {
        if let Some(&id) = self.prim_cache.get(&prim) {
            return id;
        }
        let id = self.alloc_concrete(Ty::Primitive(prim));
        self.prim_cache.insert(prim, id);
        id
    }

    /// Get the pre-allocated TyId for a name (used during inference of the name's
    /// own definition, before it has been generalized).
    fn ty_for_name_direct(&self, name: NameId) -> TyId {
        u32::from(name.into_raw()).into()
    }

    /// Get the pre-allocated TyId for an expression.
    fn ty_for_expr(&self, i: ExprId) -> TyId {
        let idx = self.module.names().len() as u32 + u32::from(i.into_raw());
        idx.into()
    }

    // ==========================================================================
    // Type annotation interning (doc comment → internal types)
    // ==========================================================================

    fn intern_known_ty(&mut self, _name: NameId, ty: ParsedTy) -> TyId {
        let free_vars = ty.free_vars();

        let subs: HashMap<TypeVarValue, TyId> = free_vars
            .iter()
            .map(|var| {
                let ty_id = match var {
                    TypeVarValue::Generic(_) => self.new_var(),
                    TypeVarValue::Reference(name) => todo!("Handle reference sub for {name}"),
                };
                (var.clone(), ty_id)
            })
            .collect();

        self.intern_parsed_ty(&ty, &subs)
    }

    fn intern_parsed_ty(
        &mut self,
        ty: &ParsedTy,
        substitutions: &HashMap<TypeVarValue, TyId>,
    ) -> TyId {
        match ty {
            ParsedTy::TyVar(var) => {
                let replacement = substitutions
                    .get(var)
                    .unwrap_or_else(|| panic!("No replacement for {var:?}"));
                *replacement
            }
            ParsedTy::Primitive(prim) => self.alloc_prim(*prim),
            ParsedTy::List(inner) => {
                let new_inner = self.intern_parsed_ty(&inner.0, substitutions);
                self.alloc_concrete(Ty::List(new_inner))
            }
            ParsedTy::Lambda { param, body } => {
                let new_param = self.intern_parsed_ty(&param.0, substitutions);
                let new_body = self.intern_parsed_ty(&body.0, substitutions);
                self.alloc_concrete(Ty::Lambda {
                    param: new_param,
                    body: new_body,
                })
            }
            ParsedTy::AttrSet(attr) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let new_v = self.intern_parsed_ty(&v.0, substitutions);
                    fields.insert(k.clone(), new_v);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_parsed_ty(&d.0, substitutions));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                }))
            }
            // Union annotations: create a fresh variable with each member as a lower bound.
            // This encodes `int | string` as a var where `int <: var` and `string <: var`.
            ParsedTy::Union(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(member_ty, var)
                        .expect("union annotation constraint should not fail");
                }
                var
            }
            // Intersection annotations: create a fresh variable with each member as an upper bound.
            // This encodes `a & b` as a var where `var <: a` and `var <: b`.
            ParsedTy::Intersection(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(var, member_ty)
                        .expect("intersection annotation constraint should not fail");
                }
                var
            }
        }
    }
}
