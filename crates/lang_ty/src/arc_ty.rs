use std::sync::Arc;

use derive_more::Debug;
use rustc_hash::FxHashMap;

use crate::{AttrSetTy, PrimitiveTy};

// ==============================================================================
// OutputTy — the canonical output representation of types
// ==============================================================================
//
// During inference we use `Ty<TyId>` which has 5 variants (no unions/intersections).
// After inference, canonicalization produces `OutputTy` which adds Union and Intersection.
// This separation makes it impossible to accidentally construct a union during inference.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OutputTy {
    #[debug("TyVar({_0:?})")]
    TyVar(u32),

    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),

    #[debug("List({_0:?})")]
    List(TyRef),

    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda { param: TyRef, body: TyRef },

    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<TyRef>),

    /// A union of types (e.g. `int | string`). Produced when different branches
    /// of if-then-else or list elements have different types.
    #[debug("Union({_0:?})")]
    Union(Vec<TyRef>),

    /// An intersection of types (e.g. `(int -> int) & (string -> string)`).
    /// Produced in negative/input positions when a variable has multiple upper bounds.
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<TyRef>),
}

/// Arc-wrapped OutputTy for recursive type structures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(pub Arc<OutputTy>);

/// The canonical output type. This is what InferenceResult maps names/exprs to.
pub type ArcTy = OutputTy;

impl From<OutputTy> for TyRef {
    fn from(value: OutputTy) -> Self {
        TyRef(Arc::new(value))
    }
}

pub type Substitutions = FxHashMap<u32, u32>;

// ==============================================================================
// Normalization and free variable collection on OutputTy
// ==============================================================================

impl OutputTy {
    /// Normalize all the ty vars to start from 0 instead
    /// of the "random" nums it has from solving.
    pub fn normalize_vars(&self) -> OutputTy {
        let free_vars = self.free_type_vars();

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, i as u32))
            .collect();

        self.normalize_inner(&subs)
    }

    pub fn normalize_inner(&self, free: &Substitutions) -> OutputTy {
        match self {
            OutputTy::TyVar(x) => {
                let new_idx = free.get(x).unwrap();
                OutputTy::TyVar(*new_idx)
            }
            OutputTy::List(inner) => OutputTy::List(inner.0.normalize_inner(free).into()),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: param.0.normalize_inner(free).into(),
                body: body.0.normalize_inner(free).into(),
            },
            OutputTy::AttrSet(attr_set_ty) => {
                OutputTy::AttrSet(attr_set_ty.normalize_inner(free))
            }
            OutputTy::Primitive(_) => self.clone(),
            OutputTy::Union(members) => OutputTy::Union(
                members
                    .iter()
                    .map(|m| m.0.normalize_inner(free).into())
                    .collect(),
            ),
            OutputTy::Intersection(members) => OutputTy::Intersection(
                members
                    .iter()
                    .map(|m| m.0.normalize_inner(free).into())
                    .collect(),
            ),
        }
    }

    /// Returns true if any Lambda in this type has a non-primitive param type.
    /// Such types can't be precisely generated in PBT because the `if param == <value>`
    /// code generation pattern doesn't fully constrain non-primitive params in
    /// SimpleSub's polarity-aware canonicalization.
    pub fn has_non_primitive_lambda_param(&self) -> bool {
        match self {
            OutputTy::Lambda { param, body } => {
                !matches!(&*param.0, OutputTy::Primitive(_) | OutputTy::TyVar(_))
                    || param.0.has_non_primitive_lambda_param()
                    || body.0.has_non_primitive_lambda_param()
            }
            OutputTy::List(inner) => inner.0.has_non_primitive_lambda_param(),
            OutputTy::AttrSet(attr) => {
                attr.fields
                    .values()
                    .any(|v| v.0.has_non_primitive_lambda_param())
                    || attr
                        .dyn_ty
                        .as_ref()
                        .is_some_and(|d| d.0.has_non_primitive_lambda_param())
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                members.iter().any(|m| m.0.has_non_primitive_lambda_param())
            }
            OutputTy::TyVar(_) | OutputTy::Primitive(_) => false,
        }
    }

    /// Returns true if this type or any of its children contains a Union or Intersection.
    pub fn contains_union_or_intersection(&self) -> bool {
        match self {
            OutputTy::Union(_) | OutputTy::Intersection(_) => true,
            OutputTy::TyVar(_) | OutputTy::Primitive(_) => false,
            OutputTy::List(inner) => inner.0.contains_union_or_intersection(),
            OutputTy::Lambda { param, body } => {
                param.0.contains_union_or_intersection()
                    || body.0.contains_union_or_intersection()
            }
            OutputTy::AttrSet(attr) => {
                attr.fields
                    .values()
                    .any(|v| v.0.contains_union_or_intersection())
                    || attr
                        .dyn_ty
                        .as_ref()
                        .is_some_and(|d| d.0.contains_union_or_intersection())
            }
        }
    }

    /// Collect free type variables in order of first appearance.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut set = Vec::new();
        match self {
            OutputTy::TyVar(x) => {
                set.push(*x);
            }
            OutputTy::List(inner) => set.extend(&inner.0.free_type_vars()),
            OutputTy::Lambda { param, body } => {
                set.extend(&param.0.free_type_vars());
                set.extend(&body.0.free_type_vars());
            }
            OutputTy::AttrSet(attr_set_ty) => {
                set.extend(attr_set_ty.free_type_vars());
            }
            OutputTy::Primitive(_) => {}
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for m in members {
                    set.extend(&m.0.free_type_vars());
                }
            }
        }

        set
    }
}

impl AttrSetTy<TyRef> {
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut set = Vec::new();
        self.fields.values().for_each(|v| {
            set.extend(&v.0.free_type_vars());
        });

        if let Some(dyn_ty) = &self.dyn_ty {
            set.extend(&dyn_ty.0.free_type_vars());
        }

        set
    }

    pub(crate) fn normalize_inner(&self, free: &Substitutions) -> Self {
        let fields = self
            .fields
            .iter()
            .map(|(k, v)| (k.clone(), v.0.normalize_inner(free).into()))
            .collect();

        let dyn_ty = self
            .dyn_ty
            .clone()
            .map(|dyn_ty| dyn_ty.0.normalize_inner(free).into());

        Self {
            fields,
            dyn_ty,
            open: self.open,
        }
    }
}
