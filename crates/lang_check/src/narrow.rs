// ==============================================================================
// Type Narrowing — condition analysis for flow-sensitive typing
// ==============================================================================
//
// Analyzes if-then-else conditions to derive type narrowings for each branch.
// When a condition like `x == null` is detected, the then-branch knows x is
// null and the else-branch knows x is not null. This eliminates false-positive
// type errors from idiomatic Nix patterns like:
//
//   if drv == null then null else drv.name
//
// The narrowing works by creating fresh type variables for each branch that
// replace the original variable during branch inference, avoiding cross-branch
// constraint contamination.

use lang_ast::{
    nameres::ResolveResult, BinOP, Expr, ExprBinOp, ExprId, Literal, NameId, NormalBinOp,
};

use super::CheckCtx;

/// What a condition tells us about a variable's type in a given branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NarrowPredicate {
    /// The variable is known to be null.
    IsNull,
    /// The variable is known to be non-null.
    IsNotNull,
}

/// A narrowing derived from a condition expression — binds a name to a
/// predicate that holds in a specific branch.
#[derive(Debug, Clone)]
pub(crate) struct NarrowBinding {
    pub name: NameId,
    pub predicate: NarrowPredicate,
}

/// The narrowings to apply in each branch of an if-then-else.
#[derive(Debug, Clone, Default)]
pub(crate) struct NarrowInfo {
    pub then_branch: Vec<NarrowBinding>,
    pub else_branch: Vec<NarrowBinding>,
}

impl CheckCtx<'_> {
    /// Analyze a condition expression to extract type narrowing information.
    ///
    /// Returns `None` if the condition doesn't match any recognized narrowing
    /// pattern. The analysis is purely syntactic — it pattern-matches on the
    /// AST structure without evaluating anything.
    pub(crate) fn analyze_condition(&self, cond: ExprId) -> Option<NarrowInfo> {
        let expr = &self.module[cond];
        match expr {
            // ── x == null / null == x / x != null / null != x ───────────
            Expr::BinOp {
                lhs,
                rhs,
                op: BinOP::Normal(NormalBinOp::Expr(op)),
            } if matches!(op, ExprBinOp::Equal | ExprBinOp::NotEqual) => {
                let is_eq = matches!(op, ExprBinOp::Equal);
                // Try both orientations: x == null and null == x.
                let binding = self
                    .try_null_comparison(*lhs, *rhs)
                    .or_else(|| self.try_null_comparison(*rhs, *lhs))?;

                let (then_pred, else_pred) = if is_eq {
                    (NarrowPredicate::IsNull, NarrowPredicate::IsNotNull)
                } else {
                    (NarrowPredicate::IsNotNull, NarrowPredicate::IsNull)
                };

                Some(NarrowInfo {
                    then_branch: vec![NarrowBinding {
                        name: binding,
                        predicate: then_pred,
                    }],
                    else_branch: vec![NarrowBinding {
                        name: binding,
                        predicate: else_pred,
                    }],
                })
            }

            // ── !cond — flip the narrowing ──────────────────────────────
            Expr::UnaryOp {
                op: rnix::ast::UnaryOpKind::Invert,
                expr: inner,
            } => {
                let mut info = self.analyze_condition(*inner)?;
                std::mem::swap(&mut info.then_branch, &mut info.else_branch);
                Some(info)
            }

            // ── isNull x / builtins.isNull x ───────────────────────────
            //
            // In the AST this is Apply { fun, arg } where fun resolves to
            // the builtin "isNull" and arg is a reference to a local name.
            Expr::Apply { fun, arg } => {
                if self.is_builtin_call(*fun, "isNull") {
                    let name = self.expr_as_local_name(*arg)?;
                    Some(NarrowInfo {
                        then_branch: vec![NarrowBinding {
                            name,
                            predicate: NarrowPredicate::IsNull,
                        }],
                        else_branch: vec![NarrowBinding {
                            name,
                            predicate: NarrowPredicate::IsNotNull,
                        }],
                    })
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    /// Check if `var_expr` is a reference to a local name and `null_expr` is
    /// the null literal (or a reference to unresolved "null"). Returns the
    /// NameId of the variable if the pattern matches.
    fn try_null_comparison(&self, var_expr: ExprId, null_expr: ExprId) -> Option<NameId> {
        // Check the null side first — cheaper.
        if !self.expr_is_null(null_expr) {
            return None;
        }
        self.expr_as_local_name(var_expr)
    }

    /// Check whether an expression is a reference to `null`.
    ///
    /// In the Nix AST, `null` is represented as `Reference("null")` — there's
    /// no separate Literal::Null variant. An unshadowed `null` has no entry in
    /// name resolution (it's handled as a keyword-like fallback in infer_reference).
    fn expr_is_null(&self, expr: ExprId) -> bool {
        matches!(
            &self.module[expr],
            Expr::Reference(name) if name == "null" && self.name_res.get(expr).is_none()
        )
    }

    /// If the expression is a Reference that resolves to a local Definition,
    /// return its NameId. Returns None for builtins, with-exprs, or unresolved
    /// names — we can only narrow locally-bound names.
    fn expr_as_local_name(&self, expr: ExprId) -> Option<NameId> {
        match &self.module[expr] {
            Expr::Reference(_) => match self.name_res.get(expr)? {
                ResolveResult::Definition(name) => Some(*name),
                _ => None,
            },
            _ => None,
        }
    }

    /// Check if `fun_expr` is a reference to a specific builtin function.
    /// Handles both direct builtin references (`isNull`) and qualified access
    /// (`builtins.isNull`).
    fn is_builtin_call(&self, fun_expr: ExprId, builtin_name: &str) -> bool {
        match &self.module[fun_expr] {
            // Direct reference: `isNull x`
            Expr::Reference(name) if name == builtin_name => {
                matches!(
                    self.name_res.get(fun_expr),
                    Some(ResolveResult::Builtin(b)) if *b == builtin_name
                )
            }
            // Qualified access: `builtins.isNull x`
            Expr::Select {
                set,
                attrpath,
                default_expr: None,
            } => {
                // set must be `builtins`, attrpath must be a single literal
                // key matching builtin_name.
                if attrpath.len() != 1 {
                    return false;
                }
                let is_builtins_ref = matches!(
                    &self.module[*set],
                    Expr::Reference(name) if name == "builtins"
                );
                if !is_builtins_ref {
                    return false;
                }
                // The attrpath element is an ExprId that should be a string
                // literal matching the builtin name.
                matches!(
                    &self.module[attrpath[0]],
                    Expr::Literal(Literal::String(s)) if s == builtin_name
                )
            }
            _ => false,
        }
    }
}
