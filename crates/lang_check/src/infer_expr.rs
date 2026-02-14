// ==============================================================================
// Single-Pass AST Inference
// ==============================================================================
//
// Replaces the two-phase generate+solve approach. Each expression is inferred
// in a single walk, calling constrain() inline. This is the SimpleSub approach
// where constraints are immediately propagated through the bounds graph.

use std::collections::BTreeMap;

use super::{CheckCtx, LocatedError, TyId};
use lang_ast::{
    nameres::ResolveResult, BinOP, BindingValue, Bindings, Expr, ExprId, InterpolPart, Literal,
    NormalBinOp, OverloadBinOp,
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

        // Record the inferred type for this expression.
        let expr_slot = self.ty_for_expr(e);
        self.constrain(ty, expr_slot).map_err(|err| self.locate_err(err))?;
        self.constrain(expr_slot, ty).map_err(|err| self.locate_err(err))?;

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

                let fun_ty = self.infer_expr(fun)?;
                let arg_ty = self.infer_expr(arg)?;
                let ret_ty = self.new_var();

                // fun_ty <: (arg_ty -> ret_ty)
                let lambda_ty = self.alloc_concrete(Ty::Lambda {
                    param: arg_ty,
                    body: ret_ty,
                });
                self.constrain(fun_ty, lambda_ty).map_err(|err| self.locate_err(err))?;

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
                    self.table.set_var_level(name_ty, self.table.current_level);
                    name_ty
                } else {
                    self.new_var()
                };

                if let Some(pat) = &pat {
                    let mut fields = BTreeMap::new();

                    for &(name, default_expr) in pat.fields.iter() {
                        let default_ty = default_expr.map(|e| self.infer_expr(e)).transpose()?;
                        let Some(name) = name else { continue };
                        let name_ty = self.ty_for_name_direct(name);
                        // Lift pattern field names to current level for generalization.
                        self.table.set_var_level(name_ty, self.table.current_level);
                        if let Some(default_ty) = default_ty {
                            self.constrain(default_ty, name_ty).map_err(|err| self.locate_err(err))?;
                        }
                        // Apply doc comment type annotations (e.g. /** type: x :: int */)
                        // to pattern fields. Without this, annotations on fields of
                        // top-level lambdas (not wrapped in a let binding) would be ignored.
                        self.apply_type_annotation(name, name_ty)?;
                        let field_text = self.module[name].text.clone();
                        fields.insert(field_text, name_ty);
                    }

                    let attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                        fields,
                        dyn_ty: None,
                        open: pat.ellipsis,
                    }));

                    self.constrain(param_ty, attr).map_err(|err| self.locate_err(err))?;
                    self.constrain(attr, param_ty).map_err(|err| self.locate_err(err))?;
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
                self.constrain(cond_ty, bool_ty).map_err(|err| self.locate_err(err))?;

                let then_ty = self.infer_expr(then_body)?;
                let else_ty = self.infer_expr(else_body)?;

                // Both branches flow into a result variable — this is where
                // union types naturally arise when branches have different types.
                let result = self.new_var();
                self.constrain(then_ty, result).map_err(|err| self.locate_err(err))?;
                self.constrain(else_ty, result).map_err(|err| self.locate_err(err))?;

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

                let ret_ty = attrpath.iter().try_fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.infer_expr(attr)?;
                    let str_ty = self.alloc_prim(PrimitiveTy::String);
                    self.constrain(attr_ty, str_ty).map_err(|err| self.locate_err(err))?;

                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => {
                            // Dynamic select keys (e.g. `s.${k}`) are not supported yet.
                            // Return a fresh variable so inference can continue for the
                            // rest of the file instead of panicking.
                            // TODO: constrain set_ty to have a dyn_ty, then return that
                            // dyn_ty as the result. This would give `s.${k}` the type
                            // of the attrset's dynamic field type instead of a completely
                            // unconstrained variable.
                            return Ok(self.new_var());
                        }
                    };

                    let value_ty = self.new_var();
                    // Constrain set_ty to have the field we're selecting.
                    let field_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                        fields: [(opt_key, value_ty)].into_iter().collect(),
                        dyn_ty: None,
                        open: true, // there may be more fields
                    }));
                    self.constrain(set_ty, field_attr).map_err(|err| self.locate_err(err))?;

                    Ok::<TyId, LocatedError>(value_ty)
                })?;

                if let Some(default_expr) = default_expr {
                    let default_ty = self.infer_expr(default_expr)?;
                    // The result is the union of the field type and the default type.
                    let union_var = self.new_var();
                    self.constrain(ret_ty, union_var).map_err(|err| self.locate_err(err))?;
                    self.constrain(default_ty, union_var).map_err(|err| self.locate_err(err))?;
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
                    self.constrain(et, elem_ty).map_err(|err| self.locate_err(err))?;
                }
                Ok(self.alloc_concrete(Ty::List(elem_ty)))
            }

            Expr::UnaryOp { op, expr } => {
                let ty = self.infer_expr(expr)?;
                match op {
                    rnix::ast::UnaryOpKind::Invert => {
                        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                        self.constrain(ty, bool_ty).map_err(|err| self.locate_err(err))?;
                        self.constrain(bool_ty, ty).map_err(|err| self.locate_err(err))?;
                        Ok(ty)
                    }
                    rnix::ast::UnaryOpKind::Negate => {
                        // Negation: constrain the operand to Number immediately.
                        // This catches errors like `-"hello"` at inference time and
                        // gives `a: -a` the type `number -> number`.
                        let number = self.alloc_prim(PrimitiveTy::Number);
                        self.constrain(ty, number).map_err(|err| self.locate_err(err))?;
                        Ok(ty)
                    }
                }
            }

            Expr::HasAttr { set, attrpath: _ } => {
                let set_ty = self.infer_expr(set)?;

                // Constrain set_ty to be an (open) attrset.
                let any_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                    fields: BTreeMap::new(),
                    dyn_ty: None,
                    open: true,
                }));
                self.constrain(set_ty, any_attr).map_err(|err| self.locate_err(err))?;

                Ok(self.alloc_prim(PrimitiveTy::Bool))
            }

            Expr::Assert { cond, body } => {
                let cond_ty = self.infer_expr(cond)?;
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain(cond_ty, bool_ty).map_err(|err| self.locate_err(err))?;

                self.infer_expr(body)
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
                    "builtins" => self.synth_builtins_attrset().map_err(|err| self.locate_err(err)),
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
                    // If the name is in poly_type_env, instantiate via extrude.
                    if let Some(&poly_ty) = self.poly_type_env.get(name) {
                        Ok(self.extrude(poly_ty, true))
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
                    }));
                    self.constrain(env_ty, field_attr).map_err(|err| self.locate_err(err))?;
                    Ok(value_ty)
                }
                ResolveResult::Builtin(name) => {
                    self.synthesize_builtin(name).map_err(|err| self.locate_err(err))
                }
            },
        }
    }

    fn infer_bin_op(
        &mut self,
        lhs: ExprId,
        rhs: ExprId,
        op: &BinOP,
    ) -> Result<TyId, LocatedError> {
        let lhs_ty = self.infer_expr(lhs)?;
        let rhs_ty = self.infer_expr(rhs)?;

        match op {
            BinOP::Overload(overload_op) => {
                let ret_ty = self.new_var();

                // For non-+ arithmetic ops (-, *, /), immediately constrain
                // both operands and the result to Number. This gives partial
                // type information even when operands are still polymorphic
                // (e.g. `a: b: a - b` → `number -> number -> number`).
                // + is excluded because it's also valid for strings and paths.
                if !overload_op.is_add() {
                    let number = self.alloc_prim(PrimitiveTy::Number);
                    self.constrain(lhs_ty, number).map_err(|err| self.locate_err(err))?;
                    self.constrain(rhs_ty, number).map_err(|err| self.locate_err(err))?;
                    self.constrain(ret_ty, number).map_err(|err| self.locate_err(err))?;
                }

                // Still push the overload for deferred full resolution, which
                // will pin to the precise type (int vs float) when both
                // operands become concrete.
                self.pending_overloads.push(PendingOverload {
                    op: *overload_op,
                    constraint: BinConstraint {
                        lhs: lhs_ty,
                        rhs: rhs_ty,
                        ret: ret_ty,
                    },
                });
                Ok(ret_ty)
            }

            BinOP::Normal(NormalBinOp::Bool(_)) => {
                let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
                self.constrain(lhs_ty, bool_ty).map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, bool_ty).map_err(|err| self.locate_err(err))?;
                Ok(bool_ty)
            }

            BinOP::Normal(NormalBinOp::Expr(_)) => {
                // Comparison/equality — both sides should be same type, returns Bool.
                self.constrain(lhs_ty, rhs_ty).map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, lhs_ty).map_err(|err| self.locate_err(err))?;

                // After equality, explicitly propagate concrete types as upper bounds.
                // The bidirectional constraint creates variable-to-variable links, but
                // if one side's concrete type is behind an intermediary (e.g. attrset
                // select result), the constrain_cache may prevent it from reaching the
                // other side's upper bounds. We fix this by explicitly adding any
                // discovered concrete type as an upper bound of the other operand.
                if let Some(concrete) = self.find_concrete(rhs_ty) {
                    let c_id = self.alloc_concrete(concrete);
                    self.constrain(lhs_ty, c_id).map_err(|err| self.locate_err(err))?;
                }
                if let Some(concrete) = self.find_concrete(lhs_ty) {
                    let c_id = self.alloc_concrete(concrete);
                    self.constrain(rhs_ty, c_id).map_err(|err| self.locate_err(err))?;
                }

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
                self.constrain(lhs_ty, lhs_list).map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_ty, rhs_list).map_err(|err| self.locate_err(err))?;

                // Each side's elements flow into the result (directional, not bidirectional).
                self.constrain(lhs_elem, result_elem).map_err(|err| self.locate_err(err))?;
                self.constrain(rhs_elem, result_elem).map_err(|err| self.locate_err(err))?;

                Ok(self.alloc_concrete(Ty::List(result_elem)))
            }

            BinOP::Normal(NormalBinOp::AttrUpdate) => {
                // attr merge: we'll handle this as a pending constraint
                let ret_ty = self.new_var();
                self.pending_merges.push(BinConstraint {
                    lhs: lhs_ty,
                    rhs: rhs_ty,
                    ret: ret_ty,
                });
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
            self.constrain(value_ty, name_ty).map_err(|err| self.locate_err(err))?;
            self.constrain(name_ty, value_ty).map_err(|err| self.locate_err(err))?;
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
                let instantiated = self.extrude(poly_ty, true);
                fields.insert(name_text, instantiated);
                continue;
            }

            let name_ty = self.ty_for_name_direct(name);
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) | BindingValue::InheritFrom(e) => {
                    self.infer_expr(e)?
                }
            };
            self.constrain(value_ty, name_ty).map_err(|err| self.locate_err(err))?;
            self.constrain(name_ty, value_ty).map_err(|err| self.locate_err(err))?;
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
}

#[derive(Debug, Clone)]
pub struct PendingOverload {
    pub op: OverloadBinOp,
    pub constraint: BinConstraint,
}

/// A deferred attrset merge constraint (`//` operator).
pub type PendingMerge = BinConstraint;
