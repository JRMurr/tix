// ==============================================================================
// Type Narrowing — condition analysis for flow-sensitive typing (AST layer)
// ==============================================================================
//
// Purely syntactic analysis of if-then-else conditions to derive type narrowings
// for each branch. Moved here from lang_check so that the SCC grouping pass
// (nameres::traverse_expr) can detect narrowing scopes during its existing AST
// walk, eliminating a duplicate pre-pass.
//
// These functions only depend on the Module, NameResolution, and binding_exprs
// — they perform no type inference.

use std::collections::HashMap;

use crate::nameres::ResolveResult;
use crate::{BinOP, Expr, ExprBinOp, ExprId, Literal, NameId, NormalBinOp};
use smol_str::SmolStr;

/// Maximum depth for tracing through local alias chains when resolving
/// builtin references (e.g. `let isNull = builtins.isNull; in isNull x`).
/// Prevents infinite loops through pathological alias chains.
const MAX_ALIAS_TRACE_DEPTH: u8 = 3;

// ==============================================================================
// Narrowing Primitive — lang_ast-local subset of primitive types
// ==============================================================================
//
// lang_ast cannot depend on lang_ty (that would create a cycle), so we define
// a narrowing-specific primitive enum here. The type checker in lang_check
// converts these to lang_ty::PrimitiveTy via a From impl.

/// Primitive types recognized by narrowing condition analysis.
///
/// This is the subset of primitive types that type-predicate builtins
/// (`isNull`, `isString`, etc.) can narrow to. It deliberately excludes
/// synthetic types like `Number` and types like `Uri` that have no
/// corresponding builtin predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NarrowPrimitive {
    Null,
    String,
    Int,
    Float,
    Bool,
    Path,
}

/// What a condition tells us about a variable's type in a given branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NarrowPredicate {
    /// The variable is known to be a specific primitive type.
    /// Covers `isNull x` (IsType(Null)), `isString x` (IsType(String)), etc.
    IsType(NarrowPrimitive),
    /// The variable is known to NOT be a specific primitive type.
    /// Covers else-branches of type predicates.
    IsNotType(NarrowPrimitive),
    /// The variable is known to have a field with this name (from `x ? field`).
    HasField(SmolStr),
    /// The variable is known to NOT have a field (else-branch of `x ? field`).
    NotHasField(SmolStr),
    /// The variable is known to be an attrset (from `isAttrs x`).
    IsAttrSet,
    /// The variable is known to be a list (from `isList x`).
    IsList,
    /// The variable is known to be a function (from `isFunction x`).
    IsFunction,
}

/// A narrowing derived from a condition expression — binds a name to a
/// predicate that holds in a specific branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NarrowBinding {
    pub name: NameId,
    pub predicate: NarrowPredicate,
}

/// The narrowings to apply in each branch of an if-then-else.
#[derive(Debug, Clone, Default)]
pub struct NarrowInfo {
    pub then_branch: Vec<NarrowBinding>,
    pub else_branch: Vec<NarrowBinding>,
}

/// Known library functions where the first argument is a boolean guard
/// and the second argument is only evaluated when the guard is true.
/// For type-narrowing purposes, the second argument is inferred as if
/// it were the then-branch of `if guard then arg else <default>`.
//
// TODO(approach-B): Replace this hardcoded list with an `@inline` annotation
// in .tix stubs. The stub would provide the function body, and the checker
// would inline it to get a real if-then-else that the existing narrowing
// handles. Key files for that:
//   - comment_parser/src/tix_decl.pest  (add @inline + body grammar)
//   - comment_parser/src/tix_collect.rs (parse annotation + body)
//   - lang_check/src/aliases.rs         (store inline bodies in registry)
//   - detect_conditional_fn becomes: lookup inline body → check if it's an
//     if-then-else on the first param → extract narrowing from that
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionalFn {
    /// lib.optionalString, lib.strings.optionalString
    OptionalString,
    /// lib.optionalAttrs, lib.attrsets.optionalAttrs
    OptionalAttrs,
    /// lib.optional, lib.lists.optional
    Optional,
    /// lib.mkIf
    MkIf,
}

/// Leaf names that identify conditional library functions.
const CONDITIONAL_FN_NAMES: &[(&str, ConditionalFn)] = &[
    ("optionalString", ConditionalFn::OptionalString),
    ("optionalAttrs", ConditionalFn::OptionalAttrs),
    ("optional", ConditionalFn::Optional),
    ("mkIf", ConditionalFn::MkIf),
];

// ==============================================================================
// Module + NameResolution convenience alias
// ==============================================================================

type NameRes = crate::NameResolution;
type Mod = crate::Module;
type BindingExprs = HashMap<NameId, ExprId>;

// ==============================================================================
// Public API — analysis entry points
// ==============================================================================

/// Analyze a condition expression to extract type narrowing information.
///
/// Returns a default (empty) `NarrowInfo` if the condition doesn't match
/// any recognized narrowing pattern. The analysis is purely syntactic — it
/// pattern-matches on the AST structure without evaluating anything.
pub fn analyze_condition(
    module: &Mod,
    name_res: &NameRes,
    binding_exprs: &BindingExprs,
    cond: ExprId,
) -> NarrowInfo {
    let expr = &module[cond];
    match expr {
        // ── x == literal / literal == x / x != literal / literal != x ─
        //
        // Recognizes equality comparisons against null, true, false, and
        // other literal values. Narrows the variable to the literal's
        // primitive type in the matching branch and its negation in the
        // other branch.
        Expr::BinOp {
            lhs,
            rhs,
            op: BinOP::Normal(NormalBinOp::Expr(op)),
        } if matches!(op, ExprBinOp::Equal | ExprBinOp::NotEqual) => {
            let is_eq = matches!(op, ExprBinOp::Equal);
            // Try both orientations: x == literal and literal == x.
            let Some((binding, prim)) = try_literal_comparison(module, name_res, *lhs, *rhs)
                .or_else(|| try_literal_comparison(module, name_res, *rhs, *lhs))
            else {
                return NarrowInfo::default();
            };

            let (then_pred, else_pred) = if is_eq {
                (
                    NarrowPredicate::IsType(prim),
                    NarrowPredicate::IsNotType(prim),
                )
            } else {
                (
                    NarrowPredicate::IsNotType(prim),
                    NarrowPredicate::IsType(prim),
                )
            };

            NarrowInfo {
                then_branch: vec![NarrowBinding {
                    name: binding,
                    predicate: then_pred,
                }],
                else_branch: vec![NarrowBinding {
                    name: binding,
                    predicate: else_pred,
                }],
            }
        }

        // ── x ? field — hasAttr narrows x to have that field ────────
        Expr::HasAttr { set, attrpath } => {
            let Some(name) = expr_as_local_name(module, name_res, *set) else {
                return NarrowInfo::default();
            };
            let Some(field) = single_static_attrpath_key(module, attrpath) else {
                return NarrowInfo::default();
            };
            NarrowInfo {
                then_branch: vec![NarrowBinding {
                    name,
                    predicate: NarrowPredicate::HasField(field.clone()),
                }],
                else_branch: vec![NarrowBinding {
                    name,
                    predicate: NarrowPredicate::NotHasField(field),
                }],
            }
        }

        // ── !cond — flip the narrowing ──────────────────────────────
        Expr::UnaryOp {
            op: rnix::ast::UnaryOpKind::Invert,
            expr: inner,
        } => {
            let mut info = analyze_condition(module, name_res, binding_exprs, *inner);
            std::mem::swap(&mut info.then_branch, &mut info.else_branch);
            info
        }

        // ── a && b — both hold in then-branch ────────────────────────
        Expr::BinOp {
            lhs,
            rhs,
            op: BinOP::Normal(NormalBinOp::Bool(crate::BoolBinOp::And)),
        } => {
            let a = analyze_condition(module, name_res, binding_exprs, *lhs);
            let b = analyze_condition(module, name_res, binding_exprs, *rhs);
            NarrowInfo {
                then_branch: [a.then_branch, b.then_branch].concat(),
                else_branch: vec![], // can't determine which guard failed
            }
        }

        // ── a || b — both fail in else-branch ────────────────────────
        Expr::BinOp {
            lhs,
            rhs,
            op: BinOP::Normal(NormalBinOp::Bool(crate::BoolBinOp::Or)),
        } => {
            let a = analyze_condition(module, name_res, binding_exprs, *lhs);
            let b = analyze_condition(module, name_res, binding_exprs, *rhs);
            NarrowInfo {
                then_branch: vec![], // can't determine which guard holds
                else_branch: [a.else_branch, b.else_branch].concat(),
            }
        }

        // ── is* builtins: isNull, isString, isInt, etc. ─────────────
        //
        // In the AST this is Apply { fun, arg } where fun resolves to
        // a builtin type predicate and arg is a reference to a local name.
        Expr::Apply { fun, arg } => {
            // All recognized type predicates and their corresponding primitive.
            const TYPE_PREDICATES: &[(&str, NarrowPrimitive)] = &[
                ("isNull", NarrowPrimitive::Null),
                ("isString", NarrowPrimitive::String),
                ("isInt", NarrowPrimitive::Int),
                ("isFloat", NarrowPrimitive::Float),
                ("isBool", NarrowPrimitive::Bool),
                ("isPath", NarrowPrimitive::Path),
            ];

            for &(builtin_name, prim) in TYPE_PREDICATES {
                if is_builtin_call(module, name_res, binding_exprs, *fun, builtin_name) {
                    let Some(name) = expr_as_local_name(module, name_res, *arg) else {
                        return NarrowInfo::default();
                    };
                    return NarrowInfo {
                        then_branch: vec![NarrowBinding {
                            name,
                            predicate: NarrowPredicate::IsType(prim),
                        }],
                        else_branch: vec![NarrowBinding {
                            name,
                            predicate: NarrowPredicate::IsNotType(prim),
                        }],
                    };
                }
            }

            // Compound-type predicates: isAttrs, isList, isFunction.
            // These narrow to compound types ({..}, [α], α → β) which
            // don't have primitive representations. Only the then-branch
            // gets narrowing — negating compound types (¬{..}) is not yet
            // supported in the solver.
            const COMPOUND_PREDICATES: &[(&str, NarrowPredicate)] = &[
                ("isAttrs", NarrowPredicate::IsAttrSet),
                ("isList", NarrowPredicate::IsList),
                ("isFunction", NarrowPredicate::IsFunction),
            ];

            for &(builtin_name, ref pred) in COMPOUND_PREDICATES {
                if is_builtin_call(module, name_res, binding_exprs, *fun, builtin_name) {
                    let Some(name) = expr_as_local_name(module, name_res, *arg) else {
                        return NarrowInfo::default();
                    };
                    return NarrowInfo {
                        then_branch: vec![NarrowBinding {
                            name,
                            predicate: pred.clone(),
                        }],
                        // No useful else-branch narrowing — negation of
                        // compound types is not yet implemented.
                        else_branch: vec![],
                    };
                }
            }

            // Also check for `builtins.hasAttr "field" x` — a curried
            // two-arg call pattern where the outer Apply has arg=x and
            // fun is itself Apply { fun: hasAttr_ref, arg: string_literal }.
            if let Some(info) =
                try_hasattr_builtin_call(module, name_res, binding_exprs, *fun, *arg)
            {
                return info;
            }

            // Fallback: recognize `lib.*.isString x` etc. by leaf name.
            // This handles nixpkgs patterns like `lib.types.isString`,
            // `lib.trivial.isFunction`, `lib.isAttrs` where the function
            // is a Select chain that doesn't resolve to a builtin.
            if let Some((leaf, name)) = try_select_chain_predicate(module, name_res, *fun, *arg) {
                for &(pred_name, prim) in TYPE_PREDICATES {
                    if leaf == pred_name {
                        return NarrowInfo {
                            then_branch: vec![NarrowBinding {
                                name,
                                predicate: NarrowPredicate::IsType(prim),
                            }],
                            else_branch: vec![NarrowBinding {
                                name,
                                predicate: NarrowPredicate::IsNotType(prim),
                            }],
                        };
                    }
                }
                for &(pred_name, ref pred) in COMPOUND_PREDICATES {
                    if leaf == pred_name {
                        return NarrowInfo {
                            then_branch: vec![NarrowBinding {
                                name,
                                predicate: pred.clone(),
                            }],
                            else_branch: vec![],
                        };
                    }
                }
            }

            NarrowInfo::default()
        }

        _ => NarrowInfo::default(),
    }
}

/// Check whether an expression refers to a known conditional library function
/// (e.g. `lib.optionalString`, `optionalString`, `lib.strings.optionalString`).
///
/// Detection uses the same leaf-name-of-Select approach as
/// `try_select_chain_predicate`: we match on the last segment of a Select
/// chain, or on a bare Reference name.
pub fn detect_conditional_fn(module: &Mod, expr: ExprId) -> Option<ConditionalFn> {
    let leaf_name: &str = match &module[expr] {
        // `lib.optionalString`, `lib.strings.optionalString`, etc.
        Expr::Select {
            attrpath,
            default_expr: None,
            ..
        } => {
            let leaf_expr = attrpath.last()?;
            match &module[*leaf_expr] {
                Expr::Literal(Literal::String(name)) => name.as_str(),
                _ => return None,
            }
        }
        // Bare reference: `optionalString` (from `with lib;` or local alias)
        Expr::Reference(name) => name.as_str(),
        _ => return None,
    };

    CONDITIONAL_FN_NAMES
        .iter()
        .find(|(name, _)| *name == leaf_name)
        .map(|(_, cf)| *cf)
}

/// Detect `Apply(conditional_fn, cond)` where conditional_fn is a known
/// conditional library function. If so, analyze `cond` for narrowing and
/// return the NarrowInfo to apply to the body argument.
pub fn detect_conditional_apply_narrowing(
    module: &Mod,
    name_res: &NameRes,
    binding_exprs: &BindingExprs,
    fun_expr: ExprId,
) -> Option<NarrowInfo> {
    let Expr::Apply {
        fun: inner_fn,
        arg: cond_expr,
    } = &module[fun_expr]
    else {
        return None;
    };

    detect_conditional_fn(module, *inner_fn)?;

    let info = analyze_condition(module, name_res, binding_exprs, *cond_expr);
    if info.then_branch.is_empty() {
        return None;
    }
    Some(info)
}

// ==============================================================================
// Internal helpers
// ==============================================================================

/// Check if `var_expr` is a reference to a local name and `literal_expr`
/// is a recognized literal (null, true, false, int, float, string, path).
/// Returns the NameId of the variable and the primitive type of the literal.
fn try_literal_comparison(
    module: &Mod,
    name_res: &NameRes,
    var_expr: ExprId,
    literal_expr: ExprId,
) -> Option<(NameId, NarrowPrimitive)> {
    let prim = expr_literal_primitive(module, name_res, literal_expr)?;
    let name = expr_as_local_name(module, name_res, var_expr)?;
    Some((name, prim))
}

/// If the expression is a literal (or a keyword like null/true/false that
/// is represented as a Reference in the AST), return the corresponding
/// NarrowPrimitive.
fn expr_literal_primitive(
    module: &Mod,
    name_res: &NameRes,
    expr: ExprId,
) -> Option<NarrowPrimitive> {
    match &module[expr] {
        // null, true, false are References in the Nix AST (no Literal variant).
        Expr::Reference(name) => {
            let is_keyword = |kw: &str| match name_res.get(expr) {
                None => true,
                Some(ResolveResult::Builtin(b)) => *b == kw,
                _ => false,
            };
            match name.as_str() {
                "null" if is_keyword("null") => Some(NarrowPrimitive::Null),
                "true" if is_keyword("true") => Some(NarrowPrimitive::Bool),
                "false" if is_keyword("false") => Some(NarrowPrimitive::Bool),
                _ => None,
            }
        }
        // Actual Literal nodes in the AST.
        Expr::Literal(lit) => match lit {
            Literal::Integer(_) => Some(NarrowPrimitive::Int),
            Literal::Float(_) => Some(NarrowPrimitive::Float),
            Literal::String(_) => Some(NarrowPrimitive::String),
            Literal::Path(_) => Some(NarrowPrimitive::Path),
            Literal::Uri => None,
        },
        _ => None,
    }
}

/// If the expression is a Reference that resolves to a local Definition,
/// return its NameId. Returns None for builtins, with-exprs, or unresolved
/// names — we can only narrow locally-bound names.
fn expr_as_local_name(module: &Mod, name_res: &NameRes, expr: ExprId) -> Option<NameId> {
    match &module[expr] {
        Expr::Reference(_) => match name_res.get(expr)? {
            ResolveResult::Definition(name) => Some(*name),
            _ => None,
        },
        _ => None,
    }
}

/// Extract a single static string key from an attrpath. Returns `None`
/// for multi-element paths or paths containing dynamic (interpolated) keys
/// — we only narrow on simple `x ? fieldName` patterns.
fn single_static_attrpath_key(module: &Mod, attrpath: &[ExprId]) -> Option<SmolStr> {
    if attrpath.len() != 1 {
        return None;
    }
    match &module[attrpath[0]] {
        Expr::Literal(Literal::String(key)) => Some(key.clone()),
        _ => None,
    }
}

/// Check for the curried `builtins.hasAttr "field" x` call pattern.
///
/// In the AST this is:
///   Apply { fun: Apply { fun: hasAttr_ref, arg: string_literal }, arg: x }
/// where hasAttr_ref resolves to the `hasAttr` builtin.
fn try_hasattr_builtin_call(
    module: &Mod,
    name_res: &NameRes,
    binding_exprs: &BindingExprs,
    fun_expr: ExprId,
    arg_expr: ExprId,
) -> Option<NarrowInfo> {
    // fun_expr must itself be an Apply: `hasAttr "field"`
    let Expr::Apply {
        fun: hasattr_ref,
        arg: field_arg,
    } = &module[fun_expr]
    else {
        return None;
    };

    // The inner function must be the `hasAttr` builtin.
    if !is_builtin_call(module, name_res, binding_exprs, *hasattr_ref, "hasAttr") {
        return None;
    }

    // The first argument must be a string literal (the field name).
    let Expr::Literal(Literal::String(field_name)) = &module[*field_arg] else {
        return None;
    };

    // The outer argument (arg_expr) must be a local name reference.
    let name = expr_as_local_name(module, name_res, arg_expr)?;

    Some(NarrowInfo {
        then_branch: vec![NarrowBinding {
            name,
            predicate: NarrowPredicate::HasField(field_name.clone()),
        }],
        else_branch: vec![NarrowBinding {
            name,
            predicate: NarrowPredicate::NotHasField(field_name.clone()),
        }],
    })
}

/// Check if `fun_expr` is a Select chain whose **leaf** segment matches a
/// known type predicate name (e.g. `lib.types.isString x` → leaf "isString"),
/// and `arg_expr` is a local name reference. Returns the leaf name and NameId.
///
/// This is the fallback for `lib.*.is*` patterns that can't be traced to a
/// builtin — we rely on the naming convention instead. The bare-name and
/// `builtins.*` paths are already handled by `is_builtin_call`, so this only
/// fires for multi-segment Selects rooted on something other than `builtins`.
fn try_select_chain_predicate(
    module: &Mod,
    name_res: &NameRes,
    fun_expr: ExprId,
    arg_expr: ExprId,
) -> Option<(SmolStr, NameId)> {
    let Expr::Select {
        set: _,
        attrpath,
        default_expr: None,
    } = &module[fun_expr]
    else {
        return None;
    };

    // Extract the leaf (last) segment of the attrpath.
    let leaf_expr = attrpath.last()?;
    let Expr::Literal(Literal::String(leaf_name)) = &module[*leaf_expr] else {
        return None;
    };

    let name = expr_as_local_name(module, name_res, arg_expr)?;
    Some((leaf_name.clone(), name))
}

/// Check if `fun_expr` is a reference to a specific builtin function.
/// Handles three cases:
///   1. Direct builtin reference: `isNull x`
///   2. Qualified access: `builtins.isNull x`
///   3. Local alias: `let isNull = builtins.isNull; in ... isNull x`
///      (includes `inherit (builtins) isNull`)
fn is_builtin_call(
    module: &Mod,
    name_res: &NameRes,
    binding_exprs: &BindingExprs,
    fun_expr: ExprId,
    builtin_name: &str,
) -> bool {
    is_builtin_expr(module, name_res, binding_exprs, fun_expr, builtin_name, 0)
}

/// Recursive helper for `is_builtin_call`. The `depth` parameter prevents
/// infinite loops through pathological alias chains.
fn is_builtin_expr(
    module: &Mod,
    name_res: &NameRes,
    binding_exprs: &BindingExprs,
    expr: ExprId,
    builtin_name: &str,
    depth: u8,
) -> bool {
    if depth > MAX_ALIAS_TRACE_DEPTH {
        return false;
    }

    match &module[expr] {
        // Direct reference: `isNull x`
        Expr::Reference(name) if name == builtin_name => {
            match name_res.get(expr) {
                // Case 1: direct builtin reference
                Some(ResolveResult::Builtin(b)) if *b == builtin_name => true,
                // Case 3: local alias — trace through the definition
                Some(ResolveResult::Definition(name_id)) => {
                    if let Some(&binding_expr) = binding_exprs.get(name_id) {
                        is_builtin_expr(
                            module,
                            name_res,
                            binding_exprs,
                            binding_expr,
                            builtin_name,
                            depth + 1,
                        )
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        // Case 2: qualified access: `builtins.isNull x`
        Expr::Select {
            set,
            attrpath,
            default_expr: None,
        } => {
            if attrpath.len() != 1 {
                return false;
            }
            let is_builtins_ref = matches!(
                &module[*set],
                Expr::Reference(name) if name == "builtins"
            );
            if !is_builtins_ref {
                return false;
            }
            matches!(
                &module[attrpath[0]],
                Expr::Literal(Literal::String(s)) if s == builtin_name
            )
        }
        _ => false,
    }
}
