use super::{RefType, Ty};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
            PrimitiveTy::String
                | PrimitiveTy::Path
                | PrimitiveTy::Float
                | PrimitiveTy::Int
                | PrimitiveTy::Number
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

impl<T: RefType> From<PrimitiveTy> for Ty<T> {
    fn from(value: PrimitiveTy) -> Self {
        Ty::Primitive(value)
    }
}
