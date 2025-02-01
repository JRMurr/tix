pub mod arc_ty;
mod attrset;
mod primitive;

#[cfg(any(test, feature = "proptest_support"))]
pub mod arbitrary;

pub use arc_ty::{ArcTy, Substitutions, TyRef};
pub use attrset::AttrSetTy;
use derive_more::Debug;
pub use primitive::PrimitiveTy;

// just to make it easy to share the constraints...
pub trait RefType: Eq + std::hash::Hash {}
impl<T> RefType for T where T: Eq + std::hash::Hash {}

// the mono type
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

#[macro_export]
macro_rules! arc_ty {
    // -- Match on known primitives -----------------------------------------
    (Null) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Null)
    };
    (Bool) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Bool)
    };
    (Int) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Int)
    };
    (Float) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Float)
    };
    (String) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::String)
    };
    (Path) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Path)
    };
    (Uri) => {
        $crate::Ty::<$crate::TyRef>::Primitive($crate::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: TyVar(N) --------------------------------------------
    (# $n:expr) => {
        $crate::Ty::<$crate::TyRef>::TyVar($n)
    };
    (TyVar($n:expr)) => {
        $crate::Ty::<$crate::TyRef>::TyVar($n)
    };

    // // -- List syntax: List(T) ---------------------------------------------
    // (List($elem:tt)) => {
    //     $crate::Ty::<$crate::TyRef>::List($crate::TyRef::from($crate::arc_ty!($elem)))
    // };
    (($($inner:tt)*)) => { $crate::arc_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::Ty::<$crate::TyRef>::List($crate::TyRef::from($crate::arc_ty!($($inner)*)))};

    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::Ty::<$crate::TyRef>::AttrSet($crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            None,
        ))
    }};

    ({ $($key:literal : $ty:tt),* $(,)?;  $rest:tt }) => {{
        $crate::Ty::<$crate::TyRef>::AttrSet($crate::AttrSetTy::<$crate::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            Some($crate::arc_ty!($rest).into()),
        ))
    }};

    // ({ $($key:literal : $ty:tt),* $(,)? }) => {{
    //     $crate::Ty::Attrset($crate::Attrset::from_internal(
    //         [
    //             $(($key, ty!($ty), $crate::AttrSource::Unknown),)*
    //         ],
    //         None,
    //     ))
    // }};

    ($arg:tt -> $($ret:tt)*) => {
        $crate::Ty::Lambda::<$crate::TyRef> {
            param: $crate::TyRef::from($crate::arc_ty!($arg)),
            body: $crate::TyRef::from($crate::arc_ty!($($ret)*)),
        }
    };



}
