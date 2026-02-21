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
    nameres::ResolveResult, BinOP, BindingValue, Bindings, Expr, ExprBinOp, ExprId, InterpolPart,
    Literal, NameId, NormalBinOp, OverloadBinOp,
};
use lang_ty::{AttrSetTy, PrimitiveTy, Ty};
use smol_str::SmolStr;

impl CheckCtx<'_> {
    /// Infer the type of an expression and record it in the expr→type map.
    pub(super) fn infer_expr(&mut self, e: ExprId) -> Result<TyId, LocatedError> {
        // Track the current expression so errors from constrain() and
        // sub-calls are attributed to the correct source location.
        self.current_expr = e;

        let ty = self.infer_expr_inner(e)?;

        // Restore current_expr — infer_expr_inner may have moved it to a
        // sub-expression. The slot-linking constraints below belong to `e`.
        self.current_expr = e;

        // Record the inferred type for this expression.
        let expr_slot = self.ty_for_expr(e);
        self.constrain(ty, expr_slot)
            .map_err(|err| self.locate_err(err))?;
        self.constrain(expr_slot, ty)
            .map_err(|err| self.locate_err(err))?;

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
                self.constrain(fun_ty, lambda_ty)
                    .map_err(|err| self.locate_err(err))?;

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
                            self.constrain(default_ty, name_ty)
                                .map_err(|err| self.locate_err(err))?;
                        }
                        // Apply doc comment type annotations (e.g. /** type: x :: int */)
                        // to pattern fields. Without this, annotations on fields of
                        // top-level lambdas (not wrapped in a let binding) would be ignored.
                        self.apply_type_annotation(name, name_ty)?;

                        // Apply context arg types (from tix.toml or /** context: <name> */).
                        // This constrains pattern fields to their declared types, e.g.
                        // `lib` gets type `Lib`, `pkgs` gets type `Pkgs`.
                        let field_text = self.module[name].text.clone();
                        if let Some(ref ctx_args) = effective_context {
                            if let Some(ctx_ty) = ctx_args.get(&field_text).cloned() {
                                let interned = self.intern_fresh_ty(ctx_ty);
                                self.constrain(interned, name_ty)
                                    .map_err(|err| self.locate_err(err))?;
                                self.constrain(name_ty, interned)
                                    .map_err(|err| self.locate_err(err))?;
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

                    self.constrain(param_ty, attr)
                        .map_err(|err| self.locate_err(err))?;
                    self.constrain(attr, param_ty)
                        .map_err(|err| self.locate_err(err))?;
                }

                let body_ty = self.infer_expr(body)?;
                Ok(self.alloc_concrete(Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                }))
            }

            Expr::BinOp { lhs, rhs, op } => self.infer_bin_op(lhs, rhs, &op),

            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain(cond_ty, bool_ty)
                    .map_err(|err| self.locate_err(err))?;

                // Analyze the condition for type narrowing opportunities.
                let narrow_info = self.analyze_condition(cond);

                let then_ty = self.infer_with_narrowing(then_body, &narrow_info, true)?;
                let else_ty = self.infer_with_narrowing(else_body, &narrow_info, false)?;

                // Both branches flow into a result variable — this is where
                // union types naturally arise when branches have different types.
                let result = self.new_var();
                self.constrain(then_ty, result)
                    .map_err(|err| self.locate_err(err))?;
                self.constrain(else_ty, result)
                    .map_err(|err| self.locate_err(err))?;

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
                    self.constrain(attr_ty, str_ty)
                        .map_err(|err| self.locate_err(err))?;

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
                            self.constrain(set_ty, dyn_attr)
                                .map_err(|err| self.locate_err(err))?;
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
                        fields: [(opt_key, value_ty)].into_iter().collect(),
                        dyn_ty: None,
                        open: true, // there may be more fields
                        optional_fields,
                    }));
                    self.constrain(set_ty, field_attr)
                        .map_err(|err| self.locate_err(err))?;

                    Ok::<TyId, LocatedError>(value_ty)
                })?;

                if let Some(default_expr) = default_expr {
                    let default_ty = self.infer_expr(default_expr)?;
                    // The result is the union of the field type and the default type.
                    let union_var = self.new_var();
                    self.constrain(ret_ty, union_var)
                        .map_err(|err| self.locate_err(err))?;
                    self.constrain(default_ty, union_var)
                        .map_err(|err| self.locate_err(err))?;
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
                    self.constrain(et, elem_ty)
                        .map_err(|err| self.locate_err(err))?;
                }
                Ok(self.alloc_concrete(Ty::List(elem_ty)))
            }

            Expr::UnaryOp { op, expr } => {
                let ty = self.infer_expr(expr)?;
                match op {
                    rnix::ast::UnaryOpKind::Invert => {
                        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                        self.constrain(ty, bool_ty)
                            .map_err(|err| self.locate_err(err))?;
                        self.constrain(bool_ty, ty)
                            .map_err(|err| self.locate_err(err))?;
                        Ok(ty)
                    }
                    rnix::ast::UnaryOpKind::Negate => {
                        // Negation: constrain the operand to Number immediately.
                        // This catches errors like `-"hello"` at inference time and
                        // gives `a: -a` the type `number -> number`.
                        let number = self.alloc_prim(PrimitiveTy::Number);
                        self.constrain(ty, number)
                            .map_err(|err| self.locate_err(err))?;
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
                    self.constrain(attr_ty, str_ty)
                        .map_err(|err| self.locate_err(err))?;
                }

                // Constrain set_ty to be an (open) attrset.
                let any_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                    fields: BTreeMap::new(),
                    dyn_ty: None,
                    open: true,
                    optional_fields: BTreeSet::new(),
                }));
                self.constrain(set_ty, any_attr)
                    .map_err(|err| self.locate_err(err))?;

                Ok(self.alloc_prim(PrimitiveTy::Bool))
            }

            Expr::Assert { cond, body } => {
                let cond_ty = self.infer_expr(cond)?;
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain(cond_ty, bool_ty)
                    .map_err(|err| self.locate_err(err))?;

                // Assert body only executes when the condition is true,
                // so apply then-branch narrowings (e.g. `assert x != null;`
                // narrows x to non-null in the body).
                let narrow_info = self.analyze_condition(cond);
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
                        Ok(self.extrude(poly_ty, Polarity::Positive))
                    } else {
                        // Not yet generalized — return the pre-allocated TyId directly.
                        Ok(self.ty_for_name_direct(name))
                    }
                }
                ResolveResult::WithExprs(innermost, _rest) => {
                    // Use the innermost `with` scope. Nix checks inner-to-outer at
                    // runtime, but statically we can only constrain one env. The
                    // innermost is the right choice for the common single-`with` case.
                    // TODO: multi-`with` fallthrough (outer env when inner lacks the field)
                    let with_expr_id = *innermost;
                    let env_id = match &self.module[with_expr_id] {
                        Expr::With { env, .. } => *env,
                        _ => unreachable!("WithExprs should reference With nodes"),
                    };

                    let env_ty = self.ty_for_expr(env_id);
                    let value_ty = self.new_var();
                    let field_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                        fields: [(var_name.clone(), value_ty)].into_iter().collect(),
                        dyn_ty: None,
                        open: true,
                        optional_fields: BTreeSet::new(),
                    }));
                    self.constrain(env_ty, field_attr)
                        .map_err(|err| self.locate_err(err))?;
                    Ok(value_ty)
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
        let Expr::Apply {
            fun: inner_fn,
            arg: cond_expr,
        } = &self.module[fun_expr]
        else {
            return None;
        };

        // Is the inner function a known conditional function?
        self.detect_conditional_fn(*inner_fn)?;

        // Extract narrowing from the condition argument.
        let info = self.analyze_condition(*cond_expr);
        if info.then_branch.is_empty() {
            // The condition didn't produce any narrowing — no point
            // wrapping the body inference.
            return None;
        }
        Some(info)
    }

    /// Create a fresh type variable for narrowing, linked to the original
    /// variable and a constraint via one-way upper bounds.
    ///
    /// Returns a fresh variable `β` where `β ≤ original` and `β ≤ constraint`.
    /// Using `add_upper_bound` directly (instead of `constrain()`) avoids
    /// bidirectional propagation — same technique as `link_extruded_var`.
    fn narrow_fresh_var(&mut self, original: TyId, constraint: TyId) -> TyId {
        let fresh = self.new_var();
        self.types.storage.add_upper_bound(fresh, original);
        self.types.storage.add_upper_bound(fresh, constraint);
        fresh
    }

    /// Compute the override TyId for a single NarrowBinding.
    ///
    /// Given a predicate and the name it narrows, returns a fresh TyId that
    /// represents the narrowed type. Shared by `infer_with_narrowing` (inline
    /// branch narrowing) and `install_binding_narrowing` (SCC-group
    /// narrowing for let-bindings under guard scopes).
    pub(crate) fn compute_narrow_override(
        &mut self,
        binding: &crate::narrow::NarrowBinding,
    ) -> TyId {
        let original_ty = self.name_slot_or_override(binding.name);

        match binding.predicate {
            crate::narrow::NarrowPredicate::IsType(prim) => {
                // α ∧ PrimType = PrimType for base types.
                self.alloc_prim(prim)
            }
            crate::narrow::NarrowPredicate::IsNotType(prim) => {
                // α ∧ ¬PrimType — fresh var linked to original and ¬Prim.
                let prim_ty = self.alloc_prim(prim);
                let neg_ty = self.alloc_concrete(Ty::Neg(prim_ty));
                self.narrow_fresh_var(original_ty, neg_ty)
            }
            crate::narrow::NarrowPredicate::HasField(ref field_name) => {
                // α ∧ {field: β}
                let fresh_field_var = self.new_var();
                let constraint = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                    fields: [(field_name.clone(), fresh_field_var)]
                        .into_iter()
                        .collect(),
                    dyn_ty: None,
                    open: true,
                    optional_fields: BTreeSet::new(),
                }));
                self.narrow_fresh_var(original_ty, constraint)
            }
            crate::narrow::NarrowPredicate::IsAttrSet => {
                // α ∧ {..}
                let constraint = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                    fields: BTreeMap::new(),
                    dyn_ty: None,
                    open: true,
                    optional_fields: BTreeSet::new(),
                }));
                self.narrow_fresh_var(original_ty, constraint)
            }
            crate::narrow::NarrowPredicate::IsList => {
                // α ∧ [β]
                let elem_var = self.new_var();
                let constraint = self.alloc_concrete(Ty::List(elem_var));
                self.narrow_fresh_var(original_ty, constraint)
            }
            crate::narrow::NarrowPredicate::IsFunction => {
                // α ∧ (β → γ)
                let param_var = self.new_var();
                let body_var = self.new_var();
                let constraint = self.alloc_concrete(Ty::Lambda {
                    param: param_var,
                    body: body_var,
                });
                self.narrow_fresh_var(original_ty, constraint)
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
                    self.constrain(lhs_ty, bound_ty)
                        .map_err(|err| self.locate_err(err))?;
                    self.constrain(rhs_ty, bound_ty)
                        .map_err(|err| self.locate_err(err))?;
                    self.constrain(ret_ty, bound_ty)
                        .map_err(|err| self.locate_err(err))?;
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
                self.constrain(lhs_ty, bool_ty)
                    .map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, bool_ty)
                    .map_err(|err| self.locate_err(err))?;
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
                self.constrain(lhs_ty, rhs_ty)
                    .map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, lhs_ty)
                    .map_err(|err| self.locate_err(err))?;
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
                self.constrain(lhs_ty, lhs_list)
                    .map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, rhs_list)
                    .map_err(|err| self.locate_err(err))?;

                // Each side's elements flow into the result (directional, not bidirectional).
                self.constrain(lhs_elem, result_elem)
                    .map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_elem, result_elem)
                    .map_err(|err| self.locate_err(err))?;

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
            self.constrain(value_ty, name_ty)
                .map_err(|err| self.locate_err(err))?;
            self.constrain(name_ty, value_ty)
                .map_err(|err| self.locate_err(err))?;
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
            self.constrain(value_ty, name_ty)
                .map_err(|err| self.locate_err(err))?;
            self.constrain(name_ty, value_ty)
                .map_err(|err| self.locate_err(err))?;
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
