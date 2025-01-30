use super::{RefType, Ty};

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

impl<T: RefType> From<crate::Literal> for Ty<T> {
    fn from(value: crate::Literal) -> Self {
        Ty::Primitive(value.into())
    }
}

impl<T: RefType> From<PrimitiveTy> for Ty<T> {
    fn from(value: PrimitiveTy) -> Self {
        Ty::Primitive(value)
    }
}
