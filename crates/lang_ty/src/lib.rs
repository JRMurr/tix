pub mod arc_ty;
mod attrset;
mod primitive;
pub mod simplify;

#[cfg(any(test, feature = "proptest_support"))]
pub mod arbitrary;

pub use arc_ty::{OutputTy, Substitutions, TyRef};
pub use attrset::AttrSetTy;
use derive_more::Debug;
pub use primitive::PrimitiveTy;

// just to make it easy to share the constraints...
pub trait RefType: Eq + std::hash::Hash {}
impl<T> RefType for T where T: Eq + std::hash::Hash {}

// The mono type — used during inference. Inter/Union are first-class
// during inference (MLstruct-style); canonicalization converts them to
// the OutputTy Union/Intersection representation for display.
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

    /// Negation type — `¬T`. Used in Boolean-Algebraic Subtyping (BAS) for
    /// precise else-branch narrowing: when `isNull x` is false, x gets type
    /// `α ∧ ¬Null` instead of a bare fresh variable.
    #[debug("Neg({_0:?})")]
    Neg(R),

    /// Intersection type — `A ∧ B`. Produced by narrowing: `Inter(α, ¬T)`
    /// means "α but not T". First-class during inference so intersections
    /// survive extrusion/generalization (MLstruct-style). Binary — multi-member
    /// composites nest: `Inter(a, Inter(b, c))`.
    #[debug("Inter({_0:?}, {_1:?})")]
    Inter(R, R),

    /// Union type — `A ∨ B`. Produced by the "annoying" constraint
    /// decomposition: `Inter(α, C) <: U` becomes `α <: Union(U, ¬C)`.
    /// Binary — multi-member composites nest.
    #[debug("Union({_0:?}, {_1:?})")]
    Union(R, R),
}

/// Macro for constructing `OutputTy` values conveniently in tests.
///
/// Supports primitives, type variables, lists, lambdas, attrsets, unions, and intersections.
///
/// NOTE: This macro is structurally duplicated as `known_ty!` in `comment_parser`.
/// If more variants are added, consider extracting a shared `impl_ty_macro!` helper.
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
    (Number) => {
        $crate::OutputTy::Primitive($crate::PrimitiveTy::Number)
    };
    // -- Bottom (never / uninhabited type) ------------------------------------
    (Bottom) => {
        $crate::OutputTy::Bottom
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

    // -- Named alias: named!("AliasName", inner_ty)
    (named!($name:expr, $inner:tt)) => {{
        $crate::OutputTy::Named(
            smol_str::SmolStr::new($name),
            $crate::TyRef::from($crate::arc_ty!($inner)),
        )
    }};

    // -- Negation: neg!(ty)
    (neg!($($inner:tt)*)) => {{
        $crate::OutputTy::Neg($crate::TyRef::from($crate::arc_ty!($($inner)*)))
    }};

    ($arg:tt -> $($ret:tt)*) => {
        $crate::OutputTy::Lambda {
            param: $crate::TyRef::from($crate::arc_ty!($arg)),
            body: $crate::TyRef::from($crate::arc_ty!($($ret)*)),
        }
    };
}
