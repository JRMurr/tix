// ==============================================================================
// Operator Dispatch Table
// ==============================================================================
//
// Centralizes the semantics of overloaded binary operators (+, -, *, /)
// into a single specification table. Previously this logic was split across
// three locations: infer_expr (immediate bounds), try_resolve_overload
// (partial/full resolution), and solve_bin_op_types (concrete dispatch).

use lang_ast::OverloadBinOp;
use lang_ty::PrimitiveTy;

/// Full specification for how an overloaded binary operator behaves.
pub struct OverloadSpec {
    /// If Some, immediately constrain both operands and result to this
    /// primitive during initial inference (before deferred resolution).
    /// Used by -, *, / to bound operands to Number right away.
    pub immediate_bound: Option<PrimitiveTy>,

    /// Given concrete lhs/rhs primitives, compute the result type.
    /// Returns None if the combination is invalid (type error).
    pub full_resolve: fn(&PrimitiveTy, &PrimitiveTy) -> Option<PrimitiveTy>,

    /// When only the lhs type is known, optionally pin the return type
    /// early. Used by + to pin string→string and path→path without
    /// waiting for the rhs.
    pub early_ret_from_lhs: fn(&PrimitiveTy) -> Option<PrimitiveTy>,
}

pub fn overload_spec(op: OverloadBinOp) -> OverloadSpec {
    match op {
        OverloadBinOp::Add => OverloadSpec {
            immediate_bound: None,
            full_resolve: resolve_add,
            early_ret_from_lhs: early_ret_add,
        },
        OverloadBinOp::Sub | OverloadBinOp::Mul | OverloadBinOp::Div => OverloadSpec {
            immediate_bound: Some(PrimitiveTy::Number),
            full_resolve: resolve_numeric_only,
            early_ret_from_lhs: no_early_ret,
        },
    }
}

// ==========================================================================
// Resolution functions
// ==========================================================================

/// `+` full resolution: handles both numeric addition and string/path concat.
fn resolve_add(lhs: &PrimitiveTy, rhs: &PrimitiveTy) -> Option<PrimitiveTy> {
    // Numeric case: float wins, Number stays Number.
    if lhs.is_number() && rhs.is_number() {
        return Some(resolve_numeric_result(lhs, rhs));
    }
    // Addable case (strings/paths): lhs type wins.
    if lhs.is_addable() && rhs.is_addable() {
        Some(*lhs)
    } else {
        None
    }
}

/// `-, *, /` full resolution: numeric types only.
fn resolve_numeric_only(lhs: &PrimitiveTy, rhs: &PrimitiveTy) -> Option<PrimitiveTy> {
    if lhs.is_number() && rhs.is_number() {
        Some(resolve_numeric_result(lhs, rhs))
    } else {
        None
    }
}

/// Compute the result primitive for two numeric operands.
/// Float wins over Int; Number stays Number unless a Float is present.
fn resolve_numeric_result(lhs: &PrimitiveTy, rhs: &PrimitiveTy) -> PrimitiveTy {
    if lhs.is_float() || rhs.is_float() {
        PrimitiveTy::Float
    } else if matches!(lhs, PrimitiveTy::Number) || matches!(rhs, PrimitiveTy::Number) {
        PrimitiveTy::Number
    } else {
        *lhs // both Int
    }
}

/// `+` early return: string→string, path→path.
fn early_ret_add(lhs: &PrimitiveTy) -> Option<PrimitiveTy> {
    match lhs {
        PrimitiveTy::String => Some(PrimitiveTy::String),
        PrimitiveTy::Path => Some(PrimitiveTy::Path),
        _ => None,
    }
}

/// No early return — used by -, *, /.
fn no_early_ret(_lhs: &PrimitiveTy) -> Option<PrimitiveTy> {
    None
}
