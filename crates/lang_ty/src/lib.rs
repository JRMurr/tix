mod attrset;
mod primitive;

use std::sync::Arc;

pub use attrset::AttrSetTy;
pub use primitive::PrimitiveTy;

use derive_more::Debug;

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(Arc<Ty<TyRef>>);

pub type ArcTy = Ty<TyRef>;

impl From<ArcTy> for TyRef {
    fn from(value: ArcTy) -> Self {
        TyRef(Arc::new(value))
    }
}

#[macro_export]
macro_rules! arc_ty {
    // -- Match on known primitives -----------------------------------------
    (Null) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Null)
    };
    (Bool) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Bool)
    };
    (Int) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Int)
    };
    (Float) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Float)
    };
    (String) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::String)
    };
    (Path) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Path)
    };
    (Uri) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Primitive($crate::ty::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: TyVar(N) --------------------------------------------
    (# $n:expr) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::TyVar($n)
    };
    (TyVar($n:expr)) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::TyVar($n)
    };

    // // -- List syntax: List(T) ---------------------------------------------
    // (List($elem:tt)) => {
    //     $crate::ty::Ty::<$crate::ty::TyRef>::List($crate::ty::TyRef::from($crate::arc_ty!($elem)))
    // };
    (($($inner:tt)*)) => { $crate::arc_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::ty::Ty::<$crate::ty::TyRef>::List($crate::ty::TyRef::from($crate::arc_ty!($($inner)*)))};

    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::ty::Ty::<$crate::ty::TyRef>::AttrSet($crate::ty::AttrSetTy::<$crate::ty::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            None,
        ))
    }};

    ({ $($key:literal : $ty:tt),* $(,)?;  $rest:tt }) => {{
        $crate::ty::Ty::<$crate::ty::TyRef>::AttrSet($crate::ty::AttrSetTy::<$crate::ty::TyRef>::from_internal(
            [
                $(($key, $crate::arc_ty!($ty)),)*
            ],
            Some($crate::arc_ty!($rest).into()),
        ))
    }};

    // ({ $($key:literal : $ty:tt),* $(,)? }) => {{
    //     $crate::ty::Ty::Attrset($crate::ty::Attrset::from_internal(
    //         [
    //             $(($key, ty!($ty), $crate::ty::AttrSource::Unknown),)*
    //         ],
    //         None,
    //     ))
    // }};

    ($arg:tt -> $($ret:tt)*) => {
        $crate::ty::Ty::Lambda::<$crate::ty::TyRef> {
            param: $crate::ty::TyRef::from($crate::arc_ty!($arg)),
            body: $crate::ty::TyRef::from($crate::arc_ty!($($ret)*)),
        }
    };



}
