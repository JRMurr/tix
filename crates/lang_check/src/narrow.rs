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
    nameres::ResolveResult, BinOP, BindingValue, Expr, ExprBinOp, ExprId, Literal, NameId,
    NormalBinOp,
};
use lang_ty::PrimitiveTy;
use smol_str::SmolStr;

use super::CheckCtx;

/// Maximum depth for tracing through local alias chains when resolving
/// builtin references (e.g. `let isNull = builtins.isNull; in isNull x`).
/// Prevents infinite loops through pathological alias chains.
const MAX_ALIAS_TRACE_DEPTH: u8 = 3;

/// What a condition tells us about a variable's type in a given branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NarrowPredicate {
    /// The variable is known to be a specific primitive type.
    /// Covers `isNull x` (IsType(Null)), `isString x` (IsType(String)), etc.
    IsType(PrimitiveTy),
    /// The variable is known to NOT be a specific primitive type.
    /// Covers else-branches of type predicates.
    IsNotType(PrimitiveTy),
    /// The variable is known to have a field with this name (from `x ? field`).
    HasField(SmolStr),
    /// The variable is known to be an attrset (from `isAttrs x`).
    IsAttrSet,
    /// The variable is known to be a list (from `isList x`).
    IsList,
    /// The variable is known to be a function (from `isFunction x`).
    IsFunction,
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
pub(crate) enum ConditionalFn {
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

impl CheckCtx<'_> {
    /// Check whether an expression refers to a known conditional library function
    /// (e.g. `lib.optionalString`, `optionalString`, `lib.strings.optionalString`).
    ///
    /// Detection uses the same leaf-name-of-Select approach as
    /// `try_select_chain_predicate`: we match on the last segment of a Select
    /// chain, or on a bare Reference name.
    pub(crate) fn detect_conditional_fn(&self, expr: ExprId) -> Option<ConditionalFn> {
        let leaf_name: &str = match &self.module[expr] {
            // `lib.optionalString`, `lib.strings.optionalString`, etc.
            Expr::Select {
                attrpath,
                default_expr: None,
                ..
            } => {
                let leaf_expr = attrpath.last()?;
                match &self.module[*leaf_expr] {
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

    /// Analyze a condition expression to extract type narrowing information.
    ///
    /// Returns a default (empty) `NarrowInfo` if the condition doesn't match
    /// any recognized narrowing pattern. The analysis is purely syntactic — it
    /// pattern-matches on the AST structure without evaluating anything.
    pub(crate) fn analyze_condition(&self, cond: ExprId) -> NarrowInfo {
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
                let Some(binding) = self
                    .try_null_comparison(*lhs, *rhs)
                    .or_else(|| self.try_null_comparison(*rhs, *lhs))
                else {
                    return NarrowInfo::default();
                };

                let (then_pred, else_pred) = if is_eq {
                    (
                        NarrowPredicate::IsType(PrimitiveTy::Null),
                        NarrowPredicate::IsNotType(PrimitiveTy::Null),
                    )
                } else {
                    (
                        NarrowPredicate::IsNotType(PrimitiveTy::Null),
                        NarrowPredicate::IsType(PrimitiveTy::Null),
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
                let Some(name) = self.expr_as_local_name(*set) else {
                    return NarrowInfo::default();
                };
                let Some(field) = self.single_static_attrpath_key(attrpath) else {
                    return NarrowInfo::default();
                };
                NarrowInfo {
                    then_branch: vec![NarrowBinding {
                        name,
                        predicate: NarrowPredicate::HasField(field),
                    }],
                    // No useful narrowing for else-branch — knowing a field
                    // is absent doesn't constrain the type in a useful way.
                    else_branch: vec![],
                }
            }

            // ── !cond — flip the narrowing ──────────────────────────────
            Expr::UnaryOp {
                op: rnix::ast::UnaryOpKind::Invert,
                expr: inner,
            } => {
                let mut info = self.analyze_condition(*inner);
                std::mem::swap(&mut info.then_branch, &mut info.else_branch);
                info
            }

            // ── is* builtins: isNull, isString, isInt, etc. ─────────────
            //
            // In the AST this is Apply { fun, arg } where fun resolves to
            // a builtin type predicate and arg is a reference to a local name.
            Expr::Apply { fun, arg } => {
                // All recognized type predicates and their corresponding primitive.
                const TYPE_PREDICATES: &[(&str, PrimitiveTy)] = &[
                    ("isNull", PrimitiveTy::Null),
                    ("isString", PrimitiveTy::String),
                    ("isInt", PrimitiveTy::Int),
                    ("isFloat", PrimitiveTy::Float),
                    ("isBool", PrimitiveTy::Bool),
                    ("isPath", PrimitiveTy::Path),
                ];

                for &(builtin_name, prim) in TYPE_PREDICATES {
                    if self.is_builtin_call(*fun, builtin_name) {
                        let Some(name) = self.expr_as_local_name(*arg) else {
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
                // don't have PrimitiveTy representations. Only the then-branch
                // gets narrowing — negating compound types (¬{..}) is not yet
                // supported in the solver.
                const COMPOUND_PREDICATES: &[(&str, NarrowPredicate)] = &[
                    ("isAttrs", NarrowPredicate::IsAttrSet),
                    ("isList", NarrowPredicate::IsList),
                    ("isFunction", NarrowPredicate::IsFunction),
                ];

                for &(builtin_name, ref pred) in COMPOUND_PREDICATES {
                    if self.is_builtin_call(*fun, builtin_name) {
                        let Some(name) = self.expr_as_local_name(*arg) else {
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
                if let Some(info) = self.try_hasattr_builtin_call(*fun, *arg) {
                    return info;
                }

                // Fallback: recognize `lib.*.isString x` etc. by leaf name.
                // This handles nixpkgs patterns like `lib.types.isString`,
                // `lib.trivial.isFunction`, `lib.isAttrs` where the function
                // is a Select chain that doesn't resolve to a builtin.
                if let Some((leaf, name)) = self.try_select_chain_predicate(*fun, *arg) {
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

    /// Extract a single static string key from an attrpath. Returns `None`
    /// for multi-element paths or paths containing dynamic (interpolated) keys
    /// — we only narrow on simple `x ? fieldName` patterns.
    fn single_static_attrpath_key(&self, attrpath: &[ExprId]) -> Option<SmolStr> {
        if attrpath.len() != 1 {
            return None;
        }
        match &self.module[attrpath[0]] {
            Expr::Literal(Literal::String(key)) => Some(key.clone()),
            _ => None,
        }
    }

    /// Check for the curried `builtins.hasAttr "field" x` call pattern.
    ///
    /// In the AST this is:
    ///   Apply { fun: Apply { fun: hasAttr_ref, arg: string_literal }, arg: x }
    /// where hasAttr_ref resolves to the `hasAttr` builtin.
    fn try_hasattr_builtin_call(&self, fun_expr: ExprId, arg_expr: ExprId) -> Option<NarrowInfo> {
        // fun_expr must itself be an Apply: `hasAttr "field"`
        let Expr::Apply {
            fun: hasattr_ref,
            arg: field_arg,
        } = &self.module[fun_expr]
        else {
            return None;
        };

        // The inner function must be the `hasAttr` builtin.
        if !self.is_builtin_call(*hasattr_ref, "hasAttr") {
            return None;
        }

        // The first argument must be a string literal (the field name).
        let Expr::Literal(Literal::String(field_name)) = &self.module[*field_arg] else {
            return None;
        };

        // The outer argument (arg_expr) must be a local name reference.
        let name = self.expr_as_local_name(arg_expr)?;

        Some(NarrowInfo {
            then_branch: vec![NarrowBinding {
                name,
                predicate: NarrowPredicate::HasField(field_name.clone()),
            }],
            // No useful narrowing for else-branch (field absence).
            else_branch: vec![],
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
        &self,
        fun_expr: ExprId,
        arg_expr: ExprId,
    ) -> Option<(SmolStr, NameId)> {
        let Expr::Select {
            set: _,
            attrpath,
            default_expr: None,
        } = &self.module[fun_expr]
        else {
            return None;
        };

        // Extract the leaf (last) segment of the attrpath.
        let leaf_expr = attrpath.last()?;
        let Expr::Literal(Literal::String(leaf_name)) = &self.module[*leaf_expr] else {
            return None;
        };

        let name = self.expr_as_local_name(arg_expr)?;
        Some((leaf_name.clone(), name))
    }

    /// Check if `fun_expr` is a reference to a specific builtin function.
    /// Handles three cases:
    ///   1. Direct builtin reference: `isNull x`
    ///   2. Qualified access: `builtins.isNull x`
    ///   3. Local alias: `let isNull = builtins.isNull; in ... isNull x`
    ///      (includes `inherit (builtins) isNull`)
    fn is_builtin_call(&self, fun_expr: ExprId, builtin_name: &str) -> bool {
        self.is_builtin_expr(fun_expr, builtin_name, 0)
    }

    /// Recursive helper for `is_builtin_call`. The `depth` parameter prevents
    /// infinite loops through pathological alias chains.
    fn is_builtin_expr(&self, expr: ExprId, builtin_name: &str, depth: u8) -> bool {
        if depth > MAX_ALIAS_TRACE_DEPTH {
            return false;
        }

        match &self.module[expr] {
            // Direct reference: `isNull x`
            Expr::Reference(name) if name == builtin_name => {
                match self.name_res.get(expr) {
                    // Case 1: direct builtin reference
                    Some(ResolveResult::Builtin(b)) if *b == builtin_name => true,
                    // Case 3: local alias — trace through the definition
                    Some(ResolveResult::Definition(name_id)) => {
                        if let Some(&binding_expr) = self.binding_exprs.get(name_id) {
                            self.is_builtin_expr(binding_expr, builtin_name, depth + 1)
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
                    &self.module[*set],
                    Expr::Reference(name) if name == "builtins"
                );
                if !is_builtins_ref {
                    return false;
                }
                matches!(
                    &self.module[attrpath[0]],
                    Expr::Literal(Literal::String(s)) if s == builtin_name
                )
            }
            _ => false,
        }
    }

    // ==========================================================================
    // Pre-pass: detect let-bindings inside narrowing scopes
    // ==========================================================================
    //
    // SCC group processing infers let-bindings *before* the if-then-else that
    // contains them installs narrowing overrides. This pre-pass walks the AST
    // purely syntactically (no type info needed) to record which bindings sit
    // inside narrowing scopes, so the SCC processing can install the right
    // overrides when inferring those bindings.

    /// Entry point: walk from the module's root expression and populate
    /// `self.binding_narrow_scopes`.
    pub(crate) fn compute_binding_narrow_scopes(&mut self) {
        let mut scopes = std::collections::HashMap::new();
        let entry = self.module.entry_expr;
        self.walk_for_narrow_scopes(entry, &[], &mut scopes);
        self.binding_narrow_scopes = scopes;
    }

    /// Recursive walk that tracks a stack of active narrowings. When we
    /// encounter a let-binding (or rec attrset binding) under active
    /// narrowings, we record those narrowings for the binding's NameId
    /// into the `scopes` map.
    fn walk_for_narrow_scopes(
        &self,
        expr: ExprId,
        active: &[NarrowBinding],
        scopes: &mut std::collections::HashMap<NameId, Vec<NarrowBinding>>,
    ) {
        let e = self.module[expr].clone();
        match e {
            // ── IfThenElse: analyze condition, push narrowings into branches
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                // Walk the condition with current narrowings (conditions don't
                // introduce new narrowings for their own sub-expressions).
                self.walk_for_narrow_scopes(cond, active, scopes);

                let info = self.analyze_condition(cond);

                // Then-branch: extend active narrowings with then_branch bindings.
                let mut then_active: Vec<NarrowBinding> = active.to_vec();
                then_active.extend(info.then_branch);
                self.walk_for_narrow_scopes(then_body, &then_active, scopes);

                // Else-branch: extend with else_branch bindings.
                let mut else_active: Vec<NarrowBinding> = active.to_vec();
                else_active.extend(info.else_branch);
                self.walk_for_narrow_scopes(else_body, &else_active, scopes);
            }

            // ── Assert: condition narrowing applies to body
            Expr::Assert { cond, body } => {
                self.walk_for_narrow_scopes(cond, active, scopes);

                let info = self.analyze_condition(cond);
                let mut body_active: Vec<NarrowBinding> = active.to_vec();
                body_active.extend(info.then_branch);
                self.walk_for_narrow_scopes(body, &body_active, scopes);
            }

            // ── Apply: detect conditional library functions
            Expr::Apply { fun, arg } => {
                let narrow_info = self.detect_conditional_apply_narrowing_prepass(fun);

                self.walk_for_narrow_scopes(fun, active, scopes);

                if let Some(info) = narrow_info {
                    let mut arg_active: Vec<NarrowBinding> = active.to_vec();
                    arg_active.extend(info.then_branch);
                    self.walk_for_narrow_scopes(arg, &arg_active, scopes);
                } else {
                    self.walk_for_narrow_scopes(arg, active, scopes);
                }
            }

            // ── LetIn: record narrowings for each binding, recurse
            Expr::LetIn { bindings, body } => {
                if !active.is_empty() {
                    for &(name, value) in bindings.statics.iter() {
                        // Record active narrowings for this binding's name.
                        scopes
                            .entry(name)
                            .or_insert_with(Vec::new)
                            .extend(active.iter().cloned());

                        match value {
                            BindingValue::Expr(e) | BindingValue::Inherit(e) => {
                                self.walk_for_narrow_scopes(e, active, scopes);
                            }
                            BindingValue::InheritFrom(_) => {}
                        }
                    }
                    for &from_expr in bindings.inherit_froms.iter() {
                        self.walk_for_narrow_scopes(from_expr, active, scopes);
                    }
                    for &(k, v) in bindings.dynamics.iter() {
                        self.walk_for_narrow_scopes(k, active, scopes);
                        self.walk_for_narrow_scopes(v, active, scopes);
                    }
                } else {
                    bindings.walk_child_exprs(|child| {
                        self.walk_for_narrow_scopes(child, active, scopes);
                    });
                }
                self.walk_for_narrow_scopes(body, active, scopes);
            }

            // ── Recursive AttrSet: same as LetIn for bindings
            Expr::AttrSet {
                is_rec: true,
                bindings,
            } => {
                if !active.is_empty() {
                    for &(name, value) in bindings.statics.iter() {
                        scopes
                            .entry(name)
                            .or_insert_with(Vec::new)
                            .extend(active.iter().cloned());
                        match value {
                            BindingValue::Expr(e) | BindingValue::Inherit(e) => {
                                self.walk_for_narrow_scopes(e, active, scopes);
                            }
                            BindingValue::InheritFrom(_) => {}
                        }
                    }
                    for &from_expr in bindings.inherit_froms.iter() {
                        self.walk_for_narrow_scopes(from_expr, active, scopes);
                    }
                    for &(k, v) in bindings.dynamics.iter() {
                        self.walk_for_narrow_scopes(k, active, scopes);
                        self.walk_for_narrow_scopes(v, active, scopes);
                    }
                } else {
                    bindings.walk_child_exprs(|child| {
                        self.walk_for_narrow_scopes(child, active, scopes);
                    });
                }
            }

            // ── Everything else: recurse into children with same narrowings
            other => {
                other.walk_child_exprs(|child| {
                    self.walk_for_narrow_scopes(child, active, scopes);
                });
            }
        }
    }

    /// Like `detect_conditional_apply_narrowing` but for the pre-pass.
    /// Checks if `fun_expr` is `Apply(conditional_fn, cond_expr)` and
    /// returns narrowing info for the body argument.
    fn detect_conditional_apply_narrowing_prepass(
        &self,
        fun_expr: ExprId,
    ) -> Option<NarrowInfo> {
        let Expr::Apply {
            fun: inner_fn,
            arg: cond_expr,
        } = &self.module[fun_expr]
        else {
            return None;
        };

        self.detect_conditional_fn(*inner_fn)?;

        let info = self.analyze_condition(*cond_expr);
        if info.then_branch.is_empty() {
            return None;
        }
        Some(info)
    }
}
