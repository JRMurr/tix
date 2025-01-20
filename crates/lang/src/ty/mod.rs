mod check;
use std::{collections::BTreeMap, sync::Arc};

pub use check::check_file;
use derive_more::Debug;
// use miette::Diagnostic;
use smol_str::SmolStr;

// the mono type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty<RefType> {
    // TODO: should specify whats a unification var vs type var
    /// A type quantifier (ie the `a` in `a -> a`)
    #[allow(clippy::enum_variant_names)]
    #[debug("TyVar({_0})")]
    TyVar(u32), // TODO: should make this u32

    // TODO: could we track literals in the type system like typescript does?
    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),

    #[debug("List({_0:?})")]
    List(RefType),
    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda { param: RefType, body: RefType },
    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<RefType>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    Null,
    Bool,
    Int,
    Float,
    String,
    Path,
    Uri,
}

impl From<crate::Literal> for PrimitiveTy {
    fn from(value: crate::Literal) -> Self {
        match value {
            crate::Literal::Float(_) => PrimitiveTy::Float,
            crate::Literal::Integer(_) => PrimitiveTy::Int,
            crate::Literal::String(_) => PrimitiveTy::String,
            crate::Literal::Path(_) => PrimitiveTy::Path,
            crate::Literal::Uri => PrimitiveTy::Uri,
        }
    }
}

impl<T> From<crate::Literal> for Ty<T> {
    fn from(value: crate::Literal) -> Self {
        Ty::Primitive(value.into())
    }
}

impl<T> From<PrimitiveTy> for Ty<T> {
    fn from(value: PrimitiveTy) -> Self {
        Ty::Primitive(value)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct AttrSetTy<RefType> {
    // TODO: i think the value here needs to be a TyId or Schema
    fields: BTreeMap<SmolStr, RefType>,

    // TODO: this only allows for one dynamic field
    // once type level literals work we should support a map of these
    dyn_ty: Option<RefType>,

    // TODO: only really used in type inference
    // https://bernsteinbear.com/blog/row-poly/
    rest: Option<RefType>,
}

impl<RefType> AttrSetTy<RefType> {
    pub fn new() -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            rest: None,
        }
    }

    pub fn from_rest(rest: RefType) -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            rest: Some(rest),
        }
    }

    pub fn keys(&self) -> std::collections::btree_map::Keys<'_, SmolStr, RefType> {
        self.fields.keys()
    }

    pub fn get(&self, key: &SmolStr) -> Option<&RefType> {
        self.fields.get(key)
    }
}

impl<RefType: Clone + Debug> AttrSetTy<RefType> {
    pub fn merge(self, other: Self) -> Self {
        // TODO: handle dyn_ty
        // TODO: not sure if this will always be the case but for now it is
        // assert!(
        //     self.rest.is_some(),
        //     "tried to merge but we don't have a rest type"
        // );
        // assert!(
        //     other.rest.is_none(),
        //     "tried to merge but other has a rest field still"
        // );

        // TODO: not sure if this should error if other has fields with the same key as self

        let mut fields: BTreeMap<SmolStr, RefType> = BTreeMap::new();

        for (k, v) in self.fields.iter().chain(other.fields.iter()) {
            fields.insert(k.clone(), v.clone());
        }

        Self {
            fields,
            dyn_ty: None, // TODO: handle
            rest: other.rest,
        }
    }

    pub fn get_sub_set(&self, keys: impl Iterator<Item = SmolStr>) -> Self {
        let mut fields = BTreeMap::new();
        for key in keys {
            let value = self
                .get(&key)
                .unwrap_or_else(|| panic!("Missing key {key}"));
            fields.insert(key, value.clone());
        }

        Self {
            fields,
            dyn_ty: self.dyn_ty.clone(),
            rest: self.rest.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[debug("{_0:?}")]
pub struct TyRef(Arc<Ty<TyRef>>);

pub type ArcTy = Ty<TyRef>;

impl From<ArcTy> for TyRef {
    fn from(value: ArcTy) -> Self {
        TyRef(Arc::new(value))
    }
}

impl AttrSetTy<TyRef> {
    pub fn from_internal<'a>(
        iter: impl IntoIterator<Item = (&'a str, Ty<TyRef>)>,
        rest: Option<TyRef>,
    ) -> Self {
        let fields: BTreeMap<SmolStr, TyRef> = iter
            .into_iter()
            .map(|(name, ty)| (SmolStr::from(name), ty.into()))
            .collect();
        // Arc::get_mut(&mut fields)
        //     .unwrap()
        //     .sort_by(|(lhs, ..), (rhs, ..)| lhs.cmp(rhs));
        // assert!(
        //     fields.windows(2).all(|w| w[0].0 != w[1].0),
        //     "Duplicated fields",
        // );
        Self {
            fields,
            rest,
            dyn_ty: None,
        }
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

    // ({ $($key:literal : $ty:tt),* $(,)? }) => {{
    //     $crate::ty::Ty::Attrset($crate::ty::Attrset::from_internal(
    //         [
    //             $(($key, ty!($ty), $crate::ty::AttrSource::Unknown),)*
    //         ],
    //         None,
    //     ))
    // }};

    ($arg:tt -> $($ret:tt)*) => {
        $crate::ty::Ty::<$crate::ty::TyRef>::Lambda {
            param: $crate::ty::TyRef::from($crate::arc_ty!($arg)),
            body: $crate::ty::TyRef::from($crate::arc_ty!($($ret)*)),
        }
    };



}
