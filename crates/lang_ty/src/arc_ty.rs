use std::sync::Arc;

use derive_more::Debug;
use rustc_hash::FxHashMap;

use crate::{AttrSetTy, Ty};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(pub Arc<Ty<TyRef>>);

pub type ArcTy = Ty<TyRef>;

impl From<ArcTy> for TyRef {
    fn from(value: ArcTy) -> Self {
        TyRef(Arc::new(value))
    }
}

pub type Substitutions = FxHashMap<u32, u32>;

impl ArcTy {
    /// Normalize all the ty vars to start from 0 instead
    /// of the "random" nums it has from solving
    pub fn normalize_vars(&self) -> ArcTy {
        let free_vars = self.free_type_vars();

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, i as u32))
            .collect();

        self.normalize_inner(&subs)
    }

    pub fn normalize_inner(&self, free: &Substitutions) -> ArcTy {
        match self {
            Ty::TyVar(x) => {
                let new_idx = free.get(x).unwrap();
                ArcTy::TyVar(*new_idx)
            }
            Ty::List(inner) => ArcTy::List(inner.0.normalize_inner(free).into()),
            Ty::Lambda { param, body } => ArcTy::Lambda {
                param: param.0.normalize_inner(free).into(),
                body: body.0.normalize_inner(free).into(),
            },
            Ty::AttrSet(attr_set_ty) => ArcTy::AttrSet(attr_set_ty.normalize_inner(free)),
            Ty::Primitive(_) => self.clone(),
            Ty::Union(union) => ArcTy::Union(
                union
                    .iter()
                    .map(|v| v.0.normalize_inner(free).into())
                    .collect(),
            ),
        }
    }

    // TODO: very similar to [CheckCtx::free_type_vars]
    // maybe there could be a generic "walk" func that could work for arena tys and arc tys?
    // or maybe i just stop having arc tys...
    // the only diff here is order sorta matters (first seen TyVar should be 'a')
    // but not end of the world if not
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut set = Vec::new();
        match self {
            Ty::TyVar(x) => {
                set.push(*x);
            }
            Ty::List(inner) => set.extend(&inner.0.free_type_vars()),
            Ty::Lambda { param, body } => {
                set.extend(&param.0.free_type_vars());
                set.extend(&body.0.free_type_vars());
            }
            Ty::AttrSet(attr_set_ty) => {
                set.extend(attr_set_ty.free_type_vars());
            }
            Ty::Primitive(_) => {}
            Ty::Union(union) => {
                for v in union.iter() {
                    set.extend(&v.0.free_type_vars());
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

        if let Some(rest_ty) = &self.rest {
            set.extend(&rest_ty.0.free_type_vars());
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

        let rest = self
            .rest
            .clone()
            .map(|rest| rest.0.normalize_inner(free).into());

        Self {
            fields,
            dyn_ty,
            rest,
        }
    }
}
