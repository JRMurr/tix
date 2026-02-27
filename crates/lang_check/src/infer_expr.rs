// ==============================================================================
// Single-Pass AST Inference
// ==============================================================================
//
// Replaces the two-phase generate+solve approach. Each expression is inferred
// in a single walk, calling constrain() inline. This is the SimpleSub approach
// where constraints are immediately propagated through the bounds graph.

use std::collections::{BTreeMap, BTreeSet};

use super::{CheckCtx, LocatedError, Polarity, TyId};
use lang_ast::{
    nameres::ResolveResult, BinOP, BindingValue, Bindings, BoolBinOp, Expr, ExprBinOp, ExprId,
    InterpolPart, Literal, NameId, NormalBinOp, OverloadBinOp,
};
use lang_ty::{AttrSetTy, PrimitiveTy, Ty};
use smol_str::SmolStr;

/// A deferred `with`-fallback constraint: the name must be found in at least
/// one of the `with` environments (tried inner-to-outer at runtime).
///
/// Each entry in `envs` is `(env_ty, value_ty)` where `env_ty` is the
/// environment's attrset type and `value_ty` is the fresh variable for the
/// field in that env. The field constraint was already added as optional, so
/// no immediate error occurs if an env doesn't have the field. During
/// `resolve_pending`, the innermost env that has the field has its value_ty
/// connected to `result`, preserving Nix's shadowing semantics.
#[derive(Debug, Clone)]
pub struct PendingWithFallback {
    /// The field name being looked up.
    pub field: SmolStr,
    /// Per-env type pairs `(env_ty, value_ty)`, ordered inner-to-outer.
    pub envs: Vec<(TyId, TyId)>,
    /// The result type variable. Connected to the winning env's value_ty
    /// during resolution.
    pub result: TyId,
    /// Location for error reporting.
    pub at_expr: ExprId,
}

impl CheckCtx<'_> {
    /// Allocate an empty open attrset type `{ ... }`.
    fn alloc_empty_open_attrset(&mut self) -> TyId {
        self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: None,
            open: true,
            optional_fields: BTreeSet::new(),
        }))
    }

    /// Allocate an open attrset type with a single field `{ field: field_ty, ... }`.
    fn alloc_single_field_open_attrset(&mut self, field: SmolStr, field_ty: TyId) -> TyId {
        self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: [(field, field_ty)].into_iter().collect(),
            dyn_ty: None,
            open: true,
            optional_fields: BTreeSet::new(),
        }))
    }

    /// Infer the type of an expression and record it in the expr→type map.
    pub(super) fn infer_expr(&mut self, e: ExprId) -> Result<TyId, LocatedError> {
        // Bail out if the deadline was exceeded (flag set by constrain()'s
        // periodic check). Return a fresh variable so callers still get a
        // valid TyId.
        if self.deadline_exceeded {
            return Ok(self.new_var());
        }

        // Track the current expression so errors from constrain() and
        // sub-calls are attributed to the correct source location.
        self.current_expr = e;

        let ty = self.infer_expr_inner(e)?;

        // Restore current_expr — infer_expr_inner may have moved it to a
        // sub-expression. The slot-linking constraints below belong to `e`.
        self.current_expr = e;

        // Record the inferred type for this expression.
        let expr_slot = self.ty_for_expr(e);
        self.constrain_equal(ty, expr_slot)?;

        Ok(ty)
    }

    fn infer_expr_inner(&mut self, e: ExprId) -> Result<TyId, LocatedError> {
        let expr = &self.module[e];
        match expr.clone() {
            Expr::Missing => Ok(self.new_var()),

            Expr::Literal(lit) => {
                let prim: PrimitiveTy = lit.into();
                Ok(self.alloc_prim(prim))
            }

            Expr::Reference(var_name) => self.infer_reference(e, &var_name),

            Expr::Apply { fun, arg } => {
                // If this Apply is a resolved import, use the pre-computed type
                // from the imported file instead of the generic `import :: a -> b`.
                if let Some(import_ty) = self.import_types.get(&e).cloned() {
                    // Still infer fun and arg so their expr→type slots are populated
                    // (needed for LSP hover/goto-def on the `import` keyword and path).
                    self.infer_expr(fun)?;
                    self.infer_expr(arg)?;
                    return Ok(self.intern_output_ty(&import_ty));
                }

                // ── Conditional library function narrowing ────────────────
                //
                // Detect `Apply(Apply(conditional_fn, cond), body)` where
                // conditional_fn is a known guard-like function (optionalString,
                // optionalAttrs, optional, mkIf). The second argument (body)
                // is only evaluated when the guard is true, so we infer it
                // under then-branch narrowing from the condition.
                let narrow_info = self.detect_conditional_apply_narrowing(fun);

                let fun_ty = self.infer_expr(fun)?;
                let arg_ty = if let Some(ref info) = narrow_info {
                    self.infer_with_narrowing(arg, info, true)?
                } else {
                    self.infer_expr(arg)?
                };
                let ret_ty = self.new_var();

                // fun_ty <: (arg_ty -> ret_ty)
                let lambda_ty = self.alloc_concrete(Ty::Lambda {
                    param: arg_ty,
                    body: ret_ty,
                });
                self.constrain_at(fun_ty, lambda_ty)?;

                Ok(ret_ty)
            }

            Expr::Lambda { param, pat, body } => {
                // Use the pre-allocated name slot directly as the Lambda's param type,
                // and lift it to the current level. This ensures:
                // 1. The Lambda param is the same TyId the body references via name resolution
                // 2. The param is at the right level for extrusion to detect it as generalizable
                // 3. Deferred overloads that reference the param TyId are found in the extrude cache
                let param_ty = if let Some(name) = param {
                    let name_ty = self.ty_for_name_direct(name);
                    self.types
                        .storage
                        .set_var_level(name_ty, self.types.storage.current_level);
                    name_ty
                } else {
                    self.new_var()
                };

                if let Some(pat) = &pat {
                    // Determine context args for this lambda. Two sources:
                    // - File-level context (from tix.toml) applies only to the root lambda
                    // - Doc comment context (/** context: nixos */) applies to any lambda
                    let effective_context =
                        if e == self.module.entry_expr && !self.context_args.is_empty() {
                            Some(self.context_args.clone())
                        } else {
                            self.resolve_doc_comment_context(e)
                        };

                    let mut fields = BTreeMap::new();
                    let mut optional = BTreeSet::new();

                    for &(name, default_expr) in pat.fields.iter() {
                        let default_ty = default_expr.map(|e| self.infer_expr(e)).transpose()?;
                        let Some(name) = name else { continue };
                        let name_ty = self.ty_for_name_direct(name);
                        // Lift pattern field names to current level for generalization.
                        self.types
                            .storage
                            .set_var_level(name_ty, self.types.storage.current_level);
                        if let Some(default_ty) = default_ty {
                            self.constrain_at(default_ty, name_ty)?;
                        }
                        // Apply doc comment type annotations and context args, unless
                        // this name was already pre-annotated before SCC groups
                        // (to avoid double-applying and creating redundant constraint paths).
                        let field_text = self.module[name].text.clone();
                        if !self.pre_annotated_params.contains(&name) {
                            self.apply_type_annotation(name, name_ty)?;

                            if let Some(ref ctx_args) = effective_context {
                                if let Some(ctx_ty) = ctx_args.get(&field_text).cloned() {
                                    let interned = self.intern_fresh_ty(ctx_ty);
                                    self.constrain_equal(interned, name_ty)?;
                                }
                            }
                        }

                        // Track fields with defaults as optional — callers may omit them.
                        if default_expr.is_some() {
                            optional.insert(field_text.clone());
                        }

                        fields.insert(field_text, name_ty);
                    }

                    let attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                        fields,
                        dyn_ty: None,
                        open: pat.ellipsis,
                        optional_fields: optional,
                    }));

                    self.constrain_equal(param_ty, attr)?;
                }

                let body_ty = self.infer_expr(body)?;
                Ok(self.alloc_concrete(Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                }))
            }

            Expr::BinOp { lhs, rhs, op } => {
                // Short-circuit narrowing for `&&` and `||`:
                //
                // `a && b` — b only evaluates when a is true, so b gets
                // then-branch narrowing from a.
                //
                // `a || b` — b only evaluates when a is false, so b gets
                // else-branch narrowing from a.
                match op {
                    BinOP::Normal(NormalBinOp::Bool(BoolBinOp::And)) => {
                        self.infer_bool_short_circuit(lhs, rhs, true)
                    }
                    BinOP::Normal(NormalBinOp::Bool(BoolBinOp::Or)) => {
                        self.infer_bool_short_circuit(lhs, rhs, false)
                    }
                    _ => self.infer_bin_op(lhs, rhs, &op),
                }
            }

            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain_at(cond_ty, bool_ty)?;

                // Analyze the condition for type narrowing opportunities.
                let narrow_info = lang_ast::narrow::analyze_condition(
                    self.module,
                    self.name_res,
                    self.binding_exprs,
                    cond,
                );

                let then_ty = self.infer_with_narrowing(then_body, &narrow_info, true)?;
                let else_ty = self.infer_with_narrowing(else_body, &narrow_info, false)?;

                // Both branches flow into a result variable — this is where
                // union types naturally arise when branches have different types.
                let result = self.new_var();
                self.constrain_at(then_ty, result)?;
                self.constrain_at(else_ty, result)?;

                Ok(result)
            }

            Expr::LetIn { bindings, body } => {
                self.infer_bindings(&bindings)?;
                self.infer_expr(body)
            }

            Expr::AttrSet {
                is_rec: _,
                bindings,
            } => {
                let attr_ty = self.infer_bindings_to_attrset(&bindings)?;
                Ok(self.alloc_concrete(Ty::AttrSet(attr_ty)))
            }

            Expr::Select {
                set,
                attrpath,
                default_expr,
            } => {
                let set_ty = self.infer_expr(set)?;

                // When a default expression is present (`x.field or default`),
                // mark each field access as optional so that missing fields
                // don't produce errors — the `or` fallback handles them.
                let has_default = default_expr.is_some();

                let ret_ty = attrpath.iter().try_fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.infer_expr(attr)?;
                    let str_ty = self.alloc_prim(PrimitiveTy::String);
                    self.constrain_at(attr_ty, str_ty)?;

                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => {
                            // Dynamic select key (e.g. `s.${k}`): constrain set_ty to
                            // have a dynamic field type and return that as the result.
                            let dyn_ty = self.new_var();
                            let dyn_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                                fields: BTreeMap::new(),
                                dyn_ty: Some(dyn_ty),
                                open: true,
                                optional_fields: BTreeSet::new(),
                            }));
                            self.constrain_at(set_ty, dyn_attr)?;
                            return Ok(dyn_ty);
                        }
                    };

                    let value_ty = self.new_var();
                    let mut optional_fields = BTreeSet::new();
                    if has_default {
                        optional_fields.insert(opt_key.clone());
                    }
                    // Constrain set_ty to have the field we're selecting.
                    let field_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                        fields: [(opt_key.clone(), value_ty)].into_iter().collect(),
                        dyn_ty: None,
                        open: true, // there may be more fields
                        optional_fields,
                    }));
                    self.constrain_at(set_ty, field_attr)?;

                    // Register a has-field obligation so that resolve_pending can
                    // re-check field presence after merges/overloads resolve.
                    // Only emit when there's no default (`or`) — defaulted field
                    // accesses are optional by design.
                    if !has_default {
                        self.deferred
                            .active
                            .push(super::PendingConstraint::HasField(PendingHasField {
                                set_ty,
                                field: opt_key,
                                field_ty: value_ty,
                                at_expr: self.current_expr,
                            }));
                    }

                    Ok::<TyId, LocatedError>(value_ty)
                })?;

                if let Some(default_expr) = default_expr {
                    let default_ty = self.infer_expr(default_expr)?;
                    // The result is the union of the field type and the default type.
                    let union_var = self.new_var();
                    self.constrain_at(ret_ty, union_var)?;
                    self.constrain_at(default_ty, union_var)?;
                    Ok(union_var)
                } else {
                    Ok(ret_ty)
                }
            }

            Expr::List(inner) => {
                // All elements flow into a single element variable.
                // Heterogeneous lists naturally produce union types.
                let elem_ty = self.new_var();
                for elem_expr in &inner {
                    let et = self.infer_expr(*elem_expr)?;
                    self.constrain_at(et, elem_ty)?;
                }
                Ok(self.alloc_concrete(Ty::List(elem_ty)))
            }

            Expr::UnaryOp { op, expr } => {
                let ty = self.infer_expr(expr)?;
                match op {
                    rnix::ast::UnaryOpKind::Invert => {
                        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                        self.constrain_equal(ty, bool_ty)?;
                        Ok(ty)
                    }
                    rnix::ast::UnaryOpKind::Negate => {
                        // Negation: constrain the operand to Number immediately.
                        // This catches errors like `-"hello"` at inference time and
                        // gives `a: -a` the type `number -> number`.
                        let number = self.alloc_prim(PrimitiveTy::Number);
                        self.constrain_at(ty, number)?;
                        Ok(ty)
                    }
                }
            }

            Expr::HasAttr { set, attrpath } => {
                let set_ty = self.infer_expr(set)?;

                // Infer attrpath elements so their expr→type slots are
                // populated (needed for LSP hover/completions on the key).
                for &attr in attrpath.iter() {
                    let attr_ty = self.infer_expr(attr)?;
                    let str_ty = self.alloc_prim(PrimitiveTy::String);
                    self.constrain_at(attr_ty, str_ty)?;
                }

                // Constrain set_ty to be an (open) attrset.
                let any_attr = self.alloc_empty_open_attrset();
                self.constrain_at(set_ty, any_attr)?;

                Ok(self.alloc_prim(PrimitiveTy::Bool))
            }

            Expr::Assert { cond, body } => {
                let cond_ty = self.infer_expr(cond)?;
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain_at(cond_ty, bool_ty)?;

                // Assert body only executes when the condition is true,
                // so apply then-branch narrowings (e.g. `assert x != null;`
                // narrows x to non-null in the body).
                let narrow_info = lang_ast::narrow::analyze_condition(
                    self.module,
                    self.name_res,
                    self.binding_exprs,
                    cond,
                );
                self.infer_with_narrowing(body, &narrow_info, true)
            }

            Expr::With { env, body } => {
                self.infer_expr(env)?;
                self.infer_expr(body)
            }
            Expr::StringInterpolation(parts) | Expr::PathInterpolation(parts) => {
                // Nix implicitly coerces interpolated sub-expressions via toString,
                // so we infer each sub-expression (to populate ty_for_expr) but don't
                // constrain its type. The overall expression is string or path.
                for part in parts.iter() {
                    if let InterpolPart::Interpol(expr_id) = part {
                        self.infer_expr(*expr_id)?;
                    }
                }
                let prim = match expr {
                    Expr::PathInterpolation(_) => PrimitiveTy::Path,
                    _ => PrimitiveTy::String,
                };
                Ok(self.alloc_prim(prim))
            }
        }
    }

    fn infer_reference(&mut self, e: ExprId, var_name: &SmolStr) -> Result<TyId, LocatedError> {
        match self.name_res.get(e) {
            None => {
                // true, false, and null can be shadowed...
                match var_name.as_str() {
                    "true" | "false" => Ok(self.alloc_prim(PrimitiveTy::Bool)),
                    "null" => Ok(self.alloc_prim(PrimitiveTy::Null)),
                    "builtins" => self
                        .synth_builtins_attrset()
                        .map_err(|err| self.locate_err(err)),
                    #[cfg(test)]
                    name if name.starts_with("__pbt_assert_") => {
                        self.infer_pbt_assert_builtin(name)
                    }
                    _ => {
                        // Check .tix global val declarations for this name.
                        if let Some(parsed_ty) =
                            self.type_aliases.global_vals().get(var_name).cloned()
                        {
                            Ok(self.intern_fresh_ty(parsed_ty))
                        } else {
                            self.emit_warning(super::Warning::UnresolvedName(var_name.clone()));
                            Ok(self.new_var())
                        }
                    }
                }
            }
            Some(res) => match res {
                &ResolveResult::Definition(name) => {
                    // Type narrowing: if we're inside a branch that narrows
                    // this name, return the branch-local override instead.
                    if let Some(&narrowed_ty) = self.narrow_overrides.get(&name) {
                        return Ok(narrowed_ty);
                    }

                    // If the name is in poly_type_env, instantiate via extrude.
                    if let Some(&poly_ty) = self.poly_type_env.get(name) {
                        let result = self.extrude(poly_ty, Polarity::Positive);
                        Ok(result)
                    } else {
                        // Not yet generalized — return the pre-allocated TyId directly.
                        Ok(self.ty_for_name_direct(name))
                    }
                }
                ResolveResult::WithExprs(innermost, rest) => {
                    // Nix evaluates nested `with` scopes inner-to-outer at
                    // runtime: the innermost scope that has the field wins.
                    //
                    // For a single `with`, we eagerly constrain as before.
                    // For multiple nested `with` scopes, we constrain each env
                    // with the field marked as optional (preventing immediate
                    // MissingField errors), and defer the selection of which
                    // env actually provides the value to `resolve_pending`.
                    // This preserves Nix's shadowing semantics: the innermost
                    // env that has the field wins.

                    let all_with_exprs: Vec<ExprId> = std::iter::once(*innermost)
                        .chain(rest.iter().copied())
                        .collect();

                    // Single `with`: fast path — no fallback needed.
                    if all_with_exprs.len() == 1 {
                        let env_id = match &self.module[all_with_exprs[0]] {
                            Expr::With { env, .. } => *env,
                            _ => unreachable!("WithExprs should reference With nodes"),
                        };
                        let env_ty = self.ty_for_expr(env_id);
                        let value_ty = self.new_var();
                        let field_attr =
                            self.alloc_single_field_open_attrset(var_name.clone(), value_ty);
                        self.constrain_at(env_ty, field_attr)?;
                        return Ok(value_ty);
                    }

                    // Multi-`with`: constrain each env with the field as
                    // optional, and collect per-env value variables. The
                    // value variables are NOT connected to the result yet —
                    // that happens in resolve_pending when we know which env
                    // actually has the field.
                    let result_ty = self.new_var();
                    let mut env_pairs: Vec<(TyId, TyId)> = Vec::new();

                    for with_expr_id in &all_with_exprs {
                        let env_id = match &self.module[*with_expr_id] {
                            Expr::With { env, .. } => *env,
                            _ => unreachable!("WithExprs should reference With nodes"),
                        };
                        let env_ty = self.ty_for_expr(env_id);
                        let value_ty = self.new_var();

                        // Mark the field as optional so a closed attrset without
                        // the field doesn't produce an immediate MissingField error.
                        let mut optional_fields = BTreeSet::new();
                        optional_fields.insert(var_name.clone());
                        let field_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                            fields: [(var_name.clone(), value_ty)].into_iter().collect(),
                            dyn_ty: None,
                            open: true,
                            optional_fields,
                        }));
                        self.constrain_at(env_ty, field_attr)?;

                        env_pairs.push((env_ty, value_ty));
                    }

                    // Deferred: find the innermost env that has the field and
                    // connect its value variable to the result.
                    self.deferred
                        .active
                        .push(super::PendingConstraint::WithFallback(
                            PendingWithFallback {
                                field: var_name.clone(),
                                envs: env_pairs,
                                result: result_ty,
                                at_expr: self.current_expr,
                            },
                        ));

                    Ok(result_ty)
                }
                ResolveResult::Builtin(name) => self
                    .synthesize_builtin(name)
                    .map_err(|err| self.locate_err(err)),
            },
        }
    }

    /// Check if `fun_expr` is `Apply(conditional_fn, cond)` where
    /// `conditional_fn` is a known conditional library function. If so,
    /// analyze `cond` for narrowing and return the NarrowInfo to apply
    /// to the body argument.
    fn detect_conditional_apply_narrowing(
        &self,
        fun_expr: ExprId,
    ) -> Option<crate::narrow::NarrowInfo> {
        lang_ast::narrow::detect_conditional_apply_narrowing(
            self.module,
            self.name_res,
            self.binding_exprs,
            fun_expr,
        )
    }

    /// Compute the override TyId for a single NarrowBinding.
    ///
    /// Given a predicate and the name it narrows, returns a TyId representing
    /// the narrowed type as `Inter(original, constraint)`. This is the
    /// MLstruct-style approach: narrowing produces first-class intersection
    /// types that survive extrusion/generalization, instead of the old
    /// side-channel fresh variables with one-way bounds.
    ///
    /// Shared by `infer_with_narrowing` (inline branch narrowing) and
    /// `install_binding_narrowing` (SCC-group narrowing for let-bindings
    /// under guard scopes).
    ///
    /// ## Design note: always using `ty_for_name_direct`
    ///
    /// All predicates use the pre-allocated name slot (`ty_for_name_direct`)
    /// as the base type in the intersection, checking existing overrides
    /// first for nested narrowing support.
    ///
    /// We intentionally bypass `poly_type_env` here because
    /// `resolve_to_concrete_id` may have collapsed a union-typed variable
    /// (e.g. `null | int`) to a single concrete type (`null`), which would
    /// make `Inter(null, ~null)` contradictory. The raw name slot variable
    /// retains all lower bounds, so the intersection correctly narrows the
    /// full type.
    pub(crate) fn compute_narrow_override(
        &mut self,
        binding: &crate::narrow::NarrowBinding,
    ) -> TyId {
        // For narrowing, use the pre-allocated name slot (raw variable) rather
        // than the poly_type_env entry. The poly_type_env entry may have been
        // resolved to a single concrete type via `resolve_to_concrete_id`,
        // which picks one of potentially many lower bounds (e.g. resolving to
        // `null` when the actual type is `null | int`). The name slot variable
        // retains all lower bounds, so `Inter(name_slot, ~Null)` correctly
        // represents "the original type minus null".
        //
        // For nested narrowing (e.g. `if isAttrs x then if x ? y`), check
        // existing overrides first so the inner narrowing builds on top.
        let original_ty = if let Some(&overridden) = self.narrow_overrides.get(&binding.name) {
            overridden
        } else {
            self.ty_for_name_direct(binding.name)
        };

        match binding.predicate {
            crate::narrow::NarrowPredicate::IsType(prim) => {
                // α ∧ PrimType — structural intersection with the primitive.
                let prim_ty = self.alloc_prim(crate::narrow::narrow_prim_to_ty(prim));
                self.alloc_concrete(Ty::Inter(original_ty, prim_ty))
            }
            crate::narrow::NarrowPredicate::IsNotType(prim) => {
                // α ∧ ¬PrimType — structural intersection with negation.
                let prim_ty = self.alloc_prim(crate::narrow::narrow_prim_to_ty(prim));
                let neg_ty = self.alloc_concrete(Ty::Neg(prim_ty));
                self.alloc_concrete(Ty::Inter(original_ty, neg_ty))
            }
            crate::narrow::NarrowPredicate::HasField(ref field_name) => {
                // α ∧ {field: β}
                let fresh_field_var = self.new_var();
                let constraint =
                    self.alloc_single_field_open_attrset(field_name.clone(), fresh_field_var);
                self.alloc_concrete(Ty::Inter(original_ty, constraint))
            }
            crate::narrow::NarrowPredicate::NotHasField(ref field_name) => {
                // α ∧ ¬{field: β, ...} — the variable does NOT have this field.
                //
                // Use the pre-allocated variable (not the resolved poly type)
                // to ensure variable isolation works in constrain_lhs_inter.
                // The poly_type_env entry may have been resolved to a concrete
                // type (e.g. a closed attrset), which lacks the variable needed
                // for MLstruct-style isolation.
                let var_ty = self.ty_for_name_direct(binding.name);
                let fresh_field_var = self.new_var();
                let has_field_ty =
                    self.alloc_single_field_open_attrset(field_name.clone(), fresh_field_var);
                let neg = self.alloc_concrete(Ty::Neg(has_field_ty));
                self.alloc_concrete(Ty::Inter(var_ty, neg))
            }
            crate::narrow::NarrowPredicate::IsAttrSet => {
                // α ∧ {..}
                let constraint = self.alloc_empty_open_attrset();
                self.alloc_concrete(Ty::Inter(original_ty, constraint))
            }
            crate::narrow::NarrowPredicate::IsList => {
                // α ∧ [β]
                let elem_var = self.new_var();
                let constraint = self.alloc_concrete(Ty::List(elem_var));
                self.alloc_concrete(Ty::Inter(original_ty, constraint))
            }
            crate::narrow::NarrowPredicate::IsFunction => {
                // α ∧ (β → γ)
                let param_var = self.new_var();
                let body_var = self.new_var();
                let constraint = self.alloc_concrete(Ty::Lambda {
                    param: param_var,
                    body: body_var,
                });
                self.alloc_concrete(Ty::Inter(original_ty, constraint))
            }
        }
    }

    /// Infer a branch body with type narrowing overrides applied.
    ///
    /// If `narrow_info` contains narrowings for the relevant branch, creates
    /// branch-local type variables and temporarily installs them as overrides
    /// in `narrow_overrides`. The overrides are removed after inference so
    /// they don't leak into sibling branches.
    fn infer_with_narrowing(
        &mut self,
        body: ExprId,
        narrow_info: &crate::narrow::NarrowInfo,
        is_then_branch: bool,
    ) -> Result<TyId, LocatedError> {
        let bindings = if is_then_branch {
            &narrow_info.then_branch
        } else {
            &narrow_info.else_branch
        };

        let saved = self.install_narrow_overrides(bindings);
        let result = self.infer_expr(body);
        self.restore_narrow_overrides(saved);

        result
    }

    /// Install narrowing overrides for a slice of NarrowBindings.
    /// Returns the saved state for restoration via `restore_narrow_overrides`.
    ///
    /// SAFETY INVARIANT: every call to `install_narrow_overrides` MUST be
    /// paired with `restore_narrow_overrides` on ALL exit paths (Ok, Err).
    /// A true RAII guard is not possible here because the guard would hold
    /// `&mut self` while the caller also needs `&mut self` for inference.
    /// If the code between install/restore panics, narrowing state is
    /// corrupted — this is acceptable because panics abort inference.
    pub(crate) fn install_narrow_overrides(
        &mut self,
        bindings: &[crate::narrow::NarrowBinding],
    ) -> Vec<(NameId, Option<TyId>)> {
        let mut saved: Vec<(NameId, Option<TyId>)> = Vec::new();

        for binding in bindings.iter() {
            let override_ty = self.compute_narrow_override(binding);
            let prev = self.narrow_overrides.insert(binding.name, override_ty);
            saved.push((binding.name, prev));
        }

        saved
    }

    /// Restore narrowing overrides from saved state. Handles nested narrowing
    /// correctly by restoring in reverse order.
    pub(crate) fn restore_narrow_overrides(&mut self, saved: Vec<(NameId, Option<TyId>)>) {
        for (name, prev) in saved.into_iter().rev() {
            match prev {
                Some(ty) => {
                    self.narrow_overrides.insert(name, ty);
                }
                None => {
                    self.narrow_overrides.remove(&name);
                }
            }
        }
    }

    /// Infer `a && b` or `a || b` with short-circuit narrowing.
    ///
    /// `is_and = true` → `&&`: RHS gets then-branch narrowing (runs when LHS is true).
    /// `is_and = false` → `||`: RHS gets else-branch narrowing (runs when LHS is false).
    fn infer_bool_short_circuit(
        &mut self,
        lhs: ExprId,
        rhs: ExprId,
        is_and: bool,
    ) -> Result<TyId, LocatedError> {
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);

        let lhs_ty = self.infer_expr(lhs)?;
        self.constrain_at(lhs_ty, bool_ty)?;

        // Analyze the LHS as a condition for narrowing.
        let narrow_info = lang_ast::narrow::analyze_condition(
            self.module,
            self.name_res,
            self.binding_exprs,
            lhs,
        );

        // Infer RHS under the appropriate narrowing branch.
        let rhs_ty = self.infer_with_narrowing(rhs, &narrow_info, is_and)?;
        self.constrain_at(rhs_ty, bool_ty)?;

        Ok(bool_ty)
    }

    fn infer_bin_op(&mut self, lhs: ExprId, rhs: ExprId, op: &BinOP) -> Result<TyId, LocatedError> {
        let lhs_ty = self.infer_expr(lhs)?;
        let rhs_ty = self.infer_expr(rhs)?;

        match op {
            BinOP::Overload(overload_op) => {
                let ret_ty = self.new_var();
                let spec = crate::operators::overload_spec(*overload_op);

                // If the operator has an immediate bound (-, *, / → Number),
                // constrain both operands and the result right away. This
                // gives partial type info even with polymorphic operands
                // (e.g. `a: b: a - b` → `number -> number -> number`).
                if let Some(bound) = spec.immediate_bound {
                    let bound_ty = self.alloc_prim(bound);
                    self.constrain_at(lhs_ty, bound_ty)?;
                    self.constrain_at(rhs_ty, bound_ty)?;
                    self.constrain_at(ret_ty, bound_ty)?;
                }

                // Still push the overload for deferred full resolution, which
                // will pin to the precise type (int vs float) when both
                // operands become concrete.
                self.deferred
                    .active
                    .push(super::PendingConstraint::Overload(PendingOverload {
                        op: *overload_op,
                        constraint: BinConstraint {
                            lhs: lhs_ty,
                            rhs: rhs_ty,
                            ret: ret_ty,
                            at_expr: self.current_expr,
                        },
                    }));
                Ok(ret_ty)
            }

            BinOP::Normal(NormalBinOp::Bool(_)) => {
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain_at(lhs_ty, bool_ty)?;
                self.constrain_at(rhs_ty, bool_ty)?;
                Ok(bool_ty)
            }

            // Equality/inequality — Nix's `==` is a total function that works
            // across types (`1 == "hi"` → false), so no type constraints are
            // imposed on the operands.
            BinOP::Normal(NormalBinOp::Expr(ExprBinOp::Equal | ExprBinOp::NotEqual)) => {
                Ok(self.alloc_prim(PrimitiveTy::Bool))
            }

            // Ordering — runtime errors on cross-type comparisons, so
            // bidirectional constraints are correct.
            BinOP::Normal(NormalBinOp::Expr(_)) => {
                self.constrain_equal(lhs_ty, rhs_ty)?;
                Ok(self.alloc_prim(PrimitiveTy::Bool))
            }

            BinOP::Normal(NormalBinOp::ListConcat) => {
                // Use separate element variables for lhs, rhs, and result so that
                // `[1] ++ ["hi"]` infers `[int | string]` instead of forcing both
                // sides to unify into one element type.
                let lhs_elem = self.new_var();
                let rhs_elem = self.new_var();
                let result_elem = self.new_var();

                let lhs_list = self.alloc_concrete(Ty::List(lhs_elem));
                let rhs_list = self.alloc_concrete(Ty::List(rhs_elem));

                // Constrain operands to be lists.
                self.constrain_at(lhs_ty, lhs_list)?;
                self.constrain_at(rhs_ty, rhs_list)?;

                // Each side's elements flow into the result (directional, not bidirectional).
                self.constrain_at(lhs_elem, result_elem)?;
                self.constrain_at(rhs_elem, result_elem)?;

                Ok(self.alloc_concrete(Ty::List(result_elem)))
            }

            BinOP::Normal(NormalBinOp::AttrUpdate) => {
                // attr merge: we'll handle this as a pending constraint
                let ret_ty = self.new_var();
                self.deferred
                    .active
                    .push(super::PendingConstraint::Merge(BinConstraint {
                        lhs: lhs_ty,
                        rhs: rhs_ty,
                        ret: ret_ty,
                        at_expr: self.current_expr,
                    }));
                Ok(ret_ty)
            }
        }
    }

    /// Infer bindings (for let-in or attrset bodies). Returns nothing for let-in,
    /// returns the AttrSetTy for attrsets.
    fn infer_bindings(&mut self, bindings: &Bindings) -> Result<(), LocatedError> {
        // Infer inherit-from expressions.
        for &from_expr in bindings.inherit_froms.iter() {
            self.infer_expr(from_expr)?;
        }

        for &(name, value) in bindings.statics.iter() {
            if self.poly_type_env.contains_idx(name) {
                // Already inferred in a previous SCC group.
                continue;
            }

            let name_ty = self.ty_for_name_direct(name);
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) | BindingValue::InheritFrom(e) => {
                    self.infer_expr(e)?
                }
            };
            // Value type flows into the name slot.
            self.constrain_equal(value_ty, name_ty)?;
        }

        Ok(())
    }

    /// Like infer_bindings, but also constructs the AttrSetTy for use in attrset expressions.
    fn infer_bindings_to_attrset(
        &mut self,
        bindings: &Bindings,
    ) -> Result<AttrSetTy<TyId>, LocatedError> {
        for &from_expr in bindings.inherit_froms.iter() {
            self.infer_expr(from_expr)?;
        }

        let mut fields = BTreeMap::new();
        for &(name, value) in bindings.statics.iter() {
            let name_text = self.module[name].text.clone();

            if let Some(&poly_ty) = self.poly_type_env.get(name) {
                // Attribute any constraint propagation errors to this binding's value.
                let (BindingValue::Inherit(e)
                | BindingValue::Expr(e)
                | BindingValue::InheritFrom(e)) = value;
                self.current_expr = e;
                let instantiated = self.extrude(poly_ty, Polarity::Positive);
                fields.insert(name_text, instantiated);
                continue;
            }

            let name_ty = self.ty_for_name_direct(name);
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) | BindingValue::InheritFrom(e) => {
                    self.infer_expr(e)?
                }
            };
            self.constrain_equal(value_ty, name_ty)?;
            fields.insert(name_text, value_ty);
        }

        let dyn_ty = if !bindings.dynamics.is_empty() {
            // TODO: infer dynamic binding types for LSP completeness.
            // A proper implementation would unify all dynamic value types into
            // a single element variable (like list inference does), constrain
            // each key to string, and set dyn_ty to that element variable.
            // This would give `{ ${k} = 1; ${j} = 2; }` the type
            // `{ _: int, ... }` instead of `{ ... }`.
            // For now, infer the expressions (to populate sub-expression types)
            // but don't track dynamic keys in the attrset type.
            for &(key_expr, value_expr) in bindings.dynamics.iter() {
                self.infer_expr(key_expr)?;
                self.infer_expr(value_expr)?;
            }
            None
        } else {
            None
        };

        Ok(AttrSetTy {
            fields,
            dyn_ty,
            open: false,
            optional_fields: BTreeSet::new(),
        })
    }

    // =========================================================================
    // PBT assertion builtins (test-only)
    // =========================================================================

    /// Synthesize the type for a `__pbt_assert_<prim>` builtin reference.
    ///
    /// Each builtin acts as an identity function with a concrete type signature
    /// (e.g. `__pbt_assert_int :: int -> int`). When PBT-generated code applies
    /// the builtin to a lambda parameter, application contravariance constrains
    /// the param to the expected primitive type — avoiding the unreliable
    /// `if param == <value>` equality trick.
    #[cfg(test)]
    fn infer_pbt_assert_builtin(&mut self, name: &str) -> Result<TyId, LocatedError> {
        let prim = match name {
            "__pbt_assert_int" => PrimitiveTy::Int,
            "__pbt_assert_float" => PrimitiveTy::Float,
            "__pbt_assert_bool" => PrimitiveTy::Bool,
            "__pbt_assert_string" => PrimitiveTy::String,
            "__pbt_assert_null" => PrimitiveTy::Null,
            _ => return Ok(self.new_var()),
        };
        let p = self.alloc_prim(prim);
        Ok(self.alloc_concrete(Ty::Lambda { param: p, body: p }))
    }
}

// ==============================================================================
// Pending constraint types for deferred resolution
// ==============================================================================

/// The lhs/rhs/ret triple shared by all deferred binary constraints.
#[derive(Debug, Clone)]
pub struct BinConstraint {
    pub lhs: TyId,
    pub rhs: TyId,
    pub ret: TyId,
    /// The expression that created this constraint, so resolution errors
    /// can be attributed to the right source location.
    pub at_expr: ExprId,
}

#[derive(Debug, Clone)]
pub struct PendingOverload {
    pub op: OverloadBinOp,
    pub constraint: BinConstraint,
}

/// A deferred attrset merge constraint (`//` operator).
pub type PendingMerge = BinConstraint;

/// A deferred has-field constraint: the set must eventually have the field,
/// and the field's type must be a subtype of the expected type.
///
/// Emitted during Select inference when the set type is not yet known to be
/// concrete. Checked during resolve_pending after merges/overloads have had
/// a chance to pin concrete types.
#[derive(Debug, Clone)]
pub struct PendingHasField {
    /// The attrset expression's type — typically a variable that may resolve
    /// to a concrete attrset.
    pub set_ty: TyId,
    /// The field that must be present.
    pub field: SmolStr,
    /// The expected field type (fresh variable created at the Select site).
    /// When the field is found, we constrain actual_field_ty <: field_ty.
    pub field_ty: TyId,
    /// Location for error reporting.
    pub at_expr: ExprId,
}
