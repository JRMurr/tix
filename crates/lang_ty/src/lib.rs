pub mod arc_ty;
mod attrset;
mod primitive;

#[cfg(any(test, feature = "proptest_support"))]
pub mod arbitrary;

use std::collections::HashSet;

pub use arc_ty::{ArcTy, OutputTy, Substitutions, TyRef};
pub use attrset::AttrSetTy;
use derive_more::Debug;
pub use primitive::PrimitiveTy;

// just to make it easy to share the constraints...
pub trait RefType: Eq + std::hash::Hash {}
impl<T> RefType for T where T: Eq + std::hash::Hash {}

// the mono type — used during inference (no Union/Intersection)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty<R, VarType = u32>
where
    R: RefType,
{
    // TODO: should specify whats a unification var vs type var
    /// A type quantifier (ie the `a` in `a -> a`)
    #[allow(clippy::enum_variant_names)]
    #[debug("TyVar({_0:?})")]
    TyVar(VarType),

    // TODO: could we track literals in the type system like typescript does?
    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),

    #[debug("List({_0:?})")]
    List(R),
    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda { param: R, body: R },
    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<R>),
}

impl<R, VarType> Ty<R, VarType>
where
    R: RefType,
    VarType: Eq + std::hash::Hash + Clone,
{
    pub fn free_vars_by_ref(ty_id: R, get_ty: &mut impl FnMut(&R) -> Self) -> HashSet<VarType> {
        let ty = get_ty(&ty_id);

        ty.free_vars(get_ty)
    }

    pub fn free_vars(&self, get_ty: &mut impl FnMut(&R) -> Self) -> HashSet<VarType> {
        let mut set = HashSet::new();

        match self {
            Ty::TyVar(var) => {
                set.insert(var.clone());
            }
            Ty::Primitive(_) => {}
            Ty::List(inner) => set.extend(get_ty(inner).free_vars(get_ty)),
            Ty::Lambda { param, body } => {
                set.extend(get_ty(param).free_vars(get_ty));
                set.extend(get_ty(body).free_vars(get_ty))
            }
            Ty::AttrSet(attr_set_ty) => {
                attr_set_ty.fields.values().for_each(|v| {
                    set.extend(get_ty(v).free_vars(get_ty));
                });

                if let Some(dyn_ty) = &attr_set_ty.dyn_ty {
                    set.extend(get_ty(dyn_ty).free_vars(get_ty))
                }
            }
        }

        set
    }
}

/// Macro for constructing `OutputTy` values conveniently in tests.
///
/// Supports primitives, type variables, lists, lambdas, attrsets, unions, and intersections.
#[macro_export]
macro_rules! arc_ty {
    // -- Match on known primitives -----------------------------------------
    (Null) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Null)
    };
    (Bool) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Bool)
    };
    (Int) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Int)
    };
    (Float) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Float)
    };
    (String) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::String)
    };
    (Path) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Path)
    };
    (Uri) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: TyVar(N) --------------------------------------------
    (# $n:expr) => {
        $crate::OutputTy::TyVar($n)
    };
    (TyVar($n:expr)) => {
        $crate::OutputTy::TyVar($n)
    };

    (($($inner:tt)*)) => { $crate::arc_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::OutputTy::List($crate::TyRef::from($crate::arc_ty!($($inner)*)))};

    // -- Closed attrset: { "key": ty, ... }
    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::OutputTy::AttrSet($crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            false,
        ))
    }};

    // -- Open attrset: { "key": ty, ... ; ... }
    ({ $($key:literal : $ty:tt),* $(,)?; ... }) => {{
        $crate::OutputTy::AttrSet($crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            true,
        ))
    }};

    // -- Union: union!(ty1, ty2, ...)
    (union!($($member:tt),+ $(,)?)) => {{
        $crate::OutputTy::Union(vec![
            $($crate::TyRef::from($crate::arc_ty!($member)),)+
        ])
    }};

    // -- Intersection: isect!(ty1, ty2, ...)
    (isect!($($member:tt),+ $(,)?)) => {{
        $crate::OutputTy::Intersection(vec![
            $($crate::TyRef::from($crate::arc_ty!($member)),)+
        ])
    }};

    ($arg:tt -> $($ret:tt)*) => {
        $crate::OutputTy::Lambda {
            param: $crate::TyRef::from($crate::arc_ty!($arg)),
            body: $crate::TyRef::from($crate::arc_ty!($($ret)*)),
        }
    };
}
