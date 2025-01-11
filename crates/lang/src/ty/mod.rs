mod check;
mod infer;
mod union_find;
use std::{collections::BTreeMap, sync::Arc};

// use miette::Diagnostic;
use smol_str::SmolStr;

pub use check::check_file_debug;

// the mono type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty<RefType> {
    // TODO: should specify whats a unification var vs type var
    /// A type quantifier (ie the `a` in `a -> a`)
    #[allow(clippy::enum_variant_names)]
    TyVar(usize),

    // TODO: could we track literals in the type system like typescript does?
    Primitive(PrimitiveTy),

    List(RefType),
    Lambda {
        param: RefType,
        body: RefType,
    },
    AttrSet(AttrSetTy<RefType>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyRef(Arc<Ty<TyRef>>);

// impl Deref for TyRef {
//     type Target = Ty<Arc<Ty<TyRef>>>;

//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }

// type ArcTyInnerRef =

pub type ArcTy = Ty<TyRef>;

impl From<ArcTy> for TyRef {
    fn from(value: ArcTy) -> Self {
        TyRef(Arc::new(value))
    }
}
