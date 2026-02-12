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
    /// Synthetic supertype of Int and Float. Not a real Nix type — used
    /// internally to constrain arithmetic operands before full resolution
    /// determines the precise numeric type.
    Number,
}

impl PrimitiveTy {
    pub fn is_number(&self) -> bool {
        matches!(
            self,
            PrimitiveTy::Float | PrimitiveTy::Int | PrimitiveTy::Number
        )
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

    /// True when `self` is a proper subtype of `other` (excluding reflexivity,
    /// which is handled separately). Currently only Int <: Number and Float <: Number.
    pub fn is_subtype_of(&self, other: &PrimitiveTy) -> bool {
        matches!(
            (self, other),
            (PrimitiveTy::Int, PrimitiveTy::Number) | (PrimitiveTy::Float, PrimitiveTy::Number)
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
