mod collect;

use std::sync::Arc;

use collect::collect_type_decls;
use derive_more::Debug;
use lang_ty::Ty;
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;
use smol_str::SmolStr;

#[derive(Parser)]
#[grammar = "comment.pest"]
pub struct CommentParser;

// box the error since rust warning about error type being too big
// TODO: is this normal for pest or is my grammar bad...
type ParseError = Box<pest::error::Error<Rule>>;

pub fn parse_comment_text(source: &str) -> Result<Pairs<Rule>, ParseError> {
    Ok(CommentParser::parse(Rule::comment_content, source)?)
}

// TODO: might worth adding this as salsa query
pub fn parse_and_collect(source: &str) -> Result<Vec<TypeDecl>, ParseError> {
    let pairs = parse_comment_text(source)?;

    Ok(collect_type_decls(pairs))
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeDecl {
    pub identifier: SmolStr,
    pub type_expr: KnownTy,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct KnownTyRef(pub Arc<Ty<KnownTyRef, TypeVarValue>>);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TypeVarValue {
    Generic(SmolStr),   // A generic with a given identifier
    Reference(SmolStr), // A reference to a different Type, should be resolved during checking
}

pub type KnownTy = Ty<KnownTyRef, TypeVarValue>;

impl From<KnownTy> for KnownTyRef {
    fn from(value: KnownTy) -> Self {
        KnownTyRef(Arc::new(value))
    }
}

// TODO: mostly copy pasted from the lang crate. Would be nice to generalize this macro to work for either type
#[macro_export]
macro_rules! known_ty {
    // -- Match on known primitives -----------------------------------------
    (null) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Null)
    };
    (bool) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Bool)
    };
    (int) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Int)
    };
    (float) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Float)
    };
    (string) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::String)
    };
    (path) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Path)
    };
    (uri) => {
        $crate::KnownTy::Primitive(::lang_ty::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: TyVar(N) --------------------------------------------
    // (TyVar($n:expr)) => {
    //     $crate::KnownTy::TyVar(($n).into())
    // };
    (# $e:expr) => {
        $crate::KnownTy::TyVar($crate::TypeVarValue::Generic(($e).into()))
    };

    // // -- List syntax: List(T) ---------------------------------------------
    // (List($elem:tt)) => {
    //     $crate::KnownTy::List($crate::ty::TyRef::from($crate::arc_ty!($elem)))
    // };
    (($($inner:tt)*)) => { $crate::known_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::KnownTy::List($crate::KnownTyRef::from($crate::known_ty!($($inner)*)))};

    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::KnownTy::AttrSet($crate::ty::AttrSetTy::<$crate::ty::TyRef>::from_internal(
            [
                $(($key, $crate::known_ty!($ty)),)*
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
        $crate::KnownTy::Lambda {
            param: $crate::KnownTyRef::from($crate::known_ty!($arg)),
            body: $crate::KnownTyRef::from($crate::known_ty!($($ret)*)),
        }
    };



}
