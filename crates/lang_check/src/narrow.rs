// ==============================================================================
// Type Narrowing — re-exports from lang_ast::narrow
// ==============================================================================
//
// The purely syntactic condition analysis now lives in lang_ast::narrow so the
// SCC grouping pass can detect narrowing scopes during its existing AST walk.
// This module re-exports the types for convenience and provides the conversion
// from NarrowPrimitive (lang_ast-local) to PrimitiveTy (lang_ty).

pub(crate) use lang_ast::narrow::{
    NarrowBinding, NarrowInfo, NarrowPredicate, NarrowPrimitive,
};
use lang_ty::PrimitiveTy;

/// Convert a narrowing-specific primitive to the type system's PrimitiveTy.
///
/// NarrowPrimitive is defined in lang_ast (which can't depend on lang_ty),
/// so this conversion lives here in lang_check which depends on both.
pub(crate) fn narrow_prim_to_ty(p: NarrowPrimitive) -> PrimitiveTy {
    match p {
        NarrowPrimitive::Null => PrimitiveTy::Null,
        NarrowPrimitive::String => PrimitiveTy::String,
        NarrowPrimitive::Int => PrimitiveTy::Int,
        NarrowPrimitive::Float => PrimitiveTy::Float,
        NarrowPrimitive::Bool => PrimitiveTy::Bool,
        NarrowPrimitive::Path => PrimitiveTy::Path,
    }
}
