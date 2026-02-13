mod collect;
pub mod tix_collect;
pub mod tix_parser;

use std::sync::Arc;

use collect::collect_type_decls;
use derive_more::Debug;
use lang_ty::{AttrSetTy, PrimitiveTy};
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;
use smol_str::SmolStr;

#[derive(Parser)]
#[grammar = "comment.pest"]
pub struct CommentParser;

// box the error since rust warning about error type being too big
// TODO: is this normal for pest or is my grammar bad...
type ParseError = Box<pest::error::Error<Rule>>;

pub fn parse_comment_text(source: &str) -> Result<Pairs<'_, Rule>, ParseError> {
    Ok(CommentParser::parse(Rule::comment_content, source)?)
}

// TODO: might worth adding this as salsa query
pub fn parse_and_collect(source: &str) -> Result<Vec<TypeDecl>, ParseError> {
    let pairs = parse_comment_text(source)?;

    Ok(collect_type_decls(pairs))
}

// =============================================================================
// .tix declaration file types and parsing
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TixDeclFile {
    pub declarations: Vec<TixDeclaration>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TixDeclaration {
    TypeAlias {
        name: SmolStr,
        body: ParsedTy,
    },
    ValDecl {
        name: SmolStr,
        ty: ParsedTy,
    },
    Module {
        name: SmolStr,
        declarations: Vec<TixDeclaration>,
    },
}

pub fn parse_tix_file(source: &str) -> Result<TixDeclFile, Box<dyn std::error::Error>> {
    use pest::Parser;
    let pairs = tix_parser::TixDeclParser::parse(tix_parser::Rule::tix_file, source)?;
    Ok(tix_collect::collect_tix_file(pairs))
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeDecl {
    pub identifier: SmolStr,
    pub type_expr: ParsedTy,
}

// =============================================================================
// Parsed type representation
// =============================================================================
//
// Standalone enum for types parsed from doc comment annotations. Includes all
// seven variants (the five from Ty<R> plus Union and Intersection) so that
// comment annotations can express the full type language. This mirrors OutputTy
// conceptually but uses TypeVarValue for type variables (named generics and
// references) instead of numeric IDs.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParsedTyRef(pub Arc<ParsedTy>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParsedTy {
    TyVar(TypeVarValue),
    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),
    #[debug("List({_0:?})")]
    List(ParsedTyRef),
    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda {
        param: ParsedTyRef,
        body: ParsedTyRef,
    },
    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<ParsedTyRef>),
    #[debug("Union({_0:?})")]
    Union(Vec<ParsedTyRef>),
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<ParsedTyRef>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeVarValue {
    Generic(SmolStr),   // A generic with a given identifier
    Reference(SmolStr), // A reference to a different Type, should be resolved during checking
}

impl From<ParsedTy> for ParsedTyRef {
    fn from(value: ParsedTy) -> Self {
        ParsedTyRef(Arc::new(value))
    }
}

impl ParsedTy {
    /// Collect all free type variables in this type.
    pub fn free_vars(&self) -> std::collections::HashSet<TypeVarValue> {
        let mut set = std::collections::HashSet::new();
        self.collect_free_vars(&mut set);
        set
    }

    fn collect_free_vars(&self, set: &mut std::collections::HashSet<TypeVarValue>) {
        match self {
            ParsedTy::TyVar(var) => {
                set.insert(var.clone());
            }
            ParsedTy::Primitive(_) => {}
            ParsedTy::List(inner) => inner.0.collect_free_vars(set),
            ParsedTy::Lambda { param, body } => {
                param.0.collect_free_vars(set);
                body.0.collect_free_vars(set);
            }
            ParsedTy::AttrSet(attr) => {
                for v in attr.fields.values() {
                    v.0.collect_free_vars(set);
                }
                if let Some(dyn_ty) = &attr.dyn_ty {
                    dyn_ty.0.collect_free_vars(set);
                }
            }
            ParsedTy::Union(members) | ParsedTy::Intersection(members) => {
                for m in members {
                    m.0.collect_free_vars(set);
                }
            }
        }
    }
}

// TODO: Structurally duplicated from `arc_ty!` in `lang_ty`. If more variants
// are added, consider extracting a shared `impl_ty_macro!` helper.
#[macro_export]
macro_rules! known_ty {
    // -- Match on known primitives -----------------------------------------
    (null) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Null)
    };
    (bool) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Bool)
    };
    (int) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Int)
    };
    (float) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Float)
    };
    (string) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::String)
    };
    (path) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Path)
    };
    (uri) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: (# "a") for generic type variables ------------------
    (# $e:expr) => {
        $crate::ParsedTy::TyVar($crate::TypeVarValue::Generic(($e).into()))
    };

    (($($inner:tt)*)) => { $crate::known_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::ParsedTy::List($crate::ParsedTyRef::from($crate::known_ty!($($inner)*)))};

    // -- Union: union!(ty1, ty2, ...) --------------------------------------
    (union!($($member:tt),+ $(,)?)) => {{
        $crate::ParsedTy::Union(vec![
            $($crate::ParsedTyRef::from($crate::known_ty!($member)),)+
        ])
    }};

    // -- Intersection: isect!(ty1, ty2, ...) --------------------------------
    (isect!($($member:tt),+ $(,)?)) => {{
        $crate::ParsedTy::Intersection(vec![
            $($crate::ParsedTyRef::from($crate::known_ty!($member)),)+
        ])
    }};

    // -- Closed attrset: { "key": ty, ... } ---------------------------------
    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: [
                $((::smol_str::SmolStr::from($key), $crate::ParsedTyRef::from($crate::known_ty!($ty))),)*
            ].into_iter().collect(),
            dyn_ty: None,
            open: false,
        })
    }};

    // -- Open attrset: { "key": ty, ... ; ... } ----------------------------
    ({ $($key:literal : $ty:tt),* $(,)?; ... }) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: [
                $((::smol_str::SmolStr::from($key), $crate::ParsedTyRef::from($crate::known_ty!($ty))),)*
            ].into_iter().collect(),
            dyn_ty: None,
            open: true,
        })
    }};

    // -- Dyn attrset: dyn_attrset!(dyn_ty) --------------------------------
    (dyn_attrset!($dyn_ty:tt)) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: std::collections::BTreeMap::new(),
            dyn_ty: Some($crate::ParsedTyRef::from($crate::known_ty!($dyn_ty))),
            open: false,
        })
    }};

    // -- Lambda: arg -> ret ------------------------------------------------
    ($arg:tt -> $($ret:tt)*) => {
        $crate::ParsedTy::Lambda {
            param: $crate::ParsedTyRef::from($crate::known_ty!($arg)),
            body: $crate::ParsedTyRef::from($crate::known_ty!($($ret)*)),
        }
    };
}
