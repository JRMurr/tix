pub mod arc_ty;
pub mod arena;
mod attrset;
pub mod disjoint;
pub mod simplify;

#[cfg(any(test, feature = "proptest_support"))]
pub mod arbitrary;

pub use arc_ty::{DisplayConfig, OutputTy, Substitutions, TyRef};
pub use arena::{OwnedTy, TypeArena, TypeDisplay};
pub use attrset::AttrSetTy;
use derive_more::Debug;
pub use primitive::PrimitiveTy;

mod primitive;

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

    /// Named type — a transparent alias wrapper. `Named(name, inner)` is
    /// semantically identical to `inner` for all type operations. Constrain
    /// unwraps it. Extrude re-wraps it. Canonicalize converts it to
    /// `OutputTy::Named`.
    #[debug("Named({_0:?}, {_1:?})")]
    Named(smol_str::SmolStr, R),

    /// A frozen (rigid) type from a cross-file import. Wraps a fully-resolved
    /// OwnedTy (arena + root index) without eagerly converting it to inference
    /// TyIds. Fields are materialized on demand when constrain encounters the
    /// Frozen type.
    #[debug("Frozen({_0:?})")]
    Frozen(crate::arena::OwnedTy),
}

/// Macro for constructing types in a TypeArena. Returns TyRef (arena index).
///
/// First argument must be a `&mut TypeArena` expression.
///
/// NOTE: This macro is structurally duplicated as `known_ty!` in `comment_parser`.
/// If more variants are added, consider extracting a shared `impl_ty_macro!` helper.
#[macro_export]
macro_rules! arc_ty {
    // -- Match on known primitives -----------------------------------------
    ($arena:expr, Null) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Null))
    };
    ($arena:expr, Bool) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Bool))
    };
    ($arena:expr, Int) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Int))
    };
    ($arena:expr, Float) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Float))
    };
    ($arena:expr, String) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::String))
    };
    ($arena:expr, Path) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Path))
    };
    ($arena:expr, Uri) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Uri))
    };
    ($arena:expr, Number) => {
        $arena.intern($crate::OutputTy::Primitive($crate::PrimitiveTy::Number))
    };
    // -- Bottom / Top -------------------------------------------------------
    ($arena:expr, Bottom) => {
        $arena.intern($crate::OutputTy::Bottom)
    };
    ($arena:expr, Top) => {
        $arena.intern($crate::OutputTy::Top)
    };
    // -- TyVar syntax: TyVar(N) or # N ------------------------------------
    ($arena:expr, # $n:expr) => {
        $arena.intern($crate::OutputTy::TyVar($n))
    };
    ($arena:expr, TyVar($n:expr)) => {
        $arena.intern($crate::OutputTy::TyVar($n))
    };

    ($arena:expr, ($($inner:tt)*)) => { $crate::arc_ty!($arena, $($inner)*) };
    ($arena:expr, [$($inner:tt)*]) => {{
        let inner = $crate::arc_ty!($arena, $($inner)*);
        $arena.intern($crate::OutputTy::List(inner))
    }};

    // -- Closed attrset: { "key": ty, ... }
    ($arena:expr, { $($key:literal : $ty:tt),* $(,)? }) => {{
        let attrset = $crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [$(($key, $crate::arc_ty!($arena, $ty)),)*],
            false,
        );
        $arena.intern($crate::OutputTy::AttrSet(attrset))
    }};

    // -- Open attrset: { "key": ty, ... ; ... }
    ($arena:expr, { $($key:literal : $ty:tt),* $(,)?; ... }) => {{
        let attrset = $crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [$(($key, $crate::arc_ty!($arena, $ty)),)*],
            true,
        );
        $arena.intern($crate::OutputTy::AttrSet(attrset))
    }};

    // -- Union: union!(ty1, ty2, ...)
    ($arena:expr, union!($($member:tt),+ $(,)?)) => {{
        $arena.intern($crate::OutputTy::Union(vec![
            $($crate::arc_ty!($arena, $member),)+
        ]))
    }};

    // -- Intersection: isect!(ty1, ty2, ...)
    ($arena:expr, isect!($($member:tt),+ $(,)?)) => {{
        $arena.intern($crate::OutputTy::Intersection(vec![
            $($crate::arc_ty!($arena, $member),)+
        ]))
    }};

    // -- Named alias: named!("AliasName", inner_ty)
    ($arena:expr, named!($name:expr, $inner:tt)) => {{
        let inner = $crate::arc_ty!($arena, $inner);
        $arena.intern($crate::OutputTy::Named(
            smol_str::SmolStr::new($name),
            inner,
        ))
    }};

    // -- Negation: neg!(ty)
    ($arena:expr, neg!($($inner:tt)*)) => {{
        let inner = $crate::arc_ty!($arena, $($inner)*);
        $arena.intern($crate::OutputTy::Neg(inner))
    }};

    ($arena:expr, $arg:tt -> $($ret:tt)*) => {{
        let param = $crate::arc_ty!($arena, $arg);
        let body = $crate::arc_ty!($arena, $($ret)*);
        $arena.intern($crate::OutputTy::Lambda {
            param,
            body,
        })
    }};
}
