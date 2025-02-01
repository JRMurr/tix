use super::{RefType, Ty};

use lang_ast::Literal;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    Null,
    Bool,
    Int,
    Float,
    String,
    Path,
    Uri,
}

impl PrimitiveTy {
    pub fn is_number(&self) -> bool {
        matches!(self, PrimitiveTy::Float | PrimitiveTy::Int)
    }

    pub fn is_float(&self) -> bool {
        matches!(self, PrimitiveTy::Float)
    }

    pub fn is_addable(&self) -> bool {
        matches!(
            self,
            PrimitiveTy::String | PrimitiveTy::Path | PrimitiveTy::Float | PrimitiveTy::Int
        )
    }
}

impl From<Literal> for PrimitiveTy {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Float(_) => PrimitiveTy::Float,
            Literal::Integer(_) => PrimitiveTy::Int,
            Literal::String(_) => PrimitiveTy::String,
            Literal::Path(_) => PrimitiveTy::Path,
            Literal::Uri => PrimitiveTy::Uri,
        }
    }
}

impl<T: RefType> From<Literal> for Ty<T> {
    fn from(value: Literal) -> Self {
        Ty::Primitive(value.into())
    }
}

impl<T: RefType> From<PrimitiveTy> for Ty<T> {
    fn from(value: PrimitiveTy) -> Self {
        Ty::Primitive(value)
    }
}
