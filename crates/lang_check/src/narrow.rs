// ==============================================================================
// Type Narrowing — re-exports from lang_ast::narrow
// ==============================================================================
//
// The purely syntactic condition analysis lives in lang_ast::narrow so the
// SCC grouping pass can detect narrowing scopes during its existing AST walk.
// Predicates carry lang_ty::PrimitiveTy directly (lang_ast depends on
// lang_ty), so no conversion layer is needed here.

pub(crate) use lang_ast::narrow::{NarrowBinding, NarrowInfo, NarrowPredicate};
