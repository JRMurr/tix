use crate::Intern;

use super::{
    AttrMergeConstraint, BinOverloadConstraint, CheckCtx, Constraint, ConstraintCtx,
    DeferrableConstraintKind, RootConstraintKind, TyId,
};
use lang_ast::{
    nameres::ResolveResult, BinOP, BindingValue, Bindings, Expr, ExprId, Literal, NormalBinOp,
};
use lang_ty::{AttrSetTy, PrimitiveTy, Ty};
use smol_str::SmolStr;
use std::collections::BTreeMap;

impl CheckCtx<'_> {
    pub(super) fn generate_constraints(
        &mut self,
        constraints: &mut ConstraintCtx,
        e: ExprId,
    ) -> TyId {
        let ty = self.generate_constraints_inner(constraints, e);
        constraints.add(Constraint {
            kind: RootConstraintKind::Eq(self.ty_for_expr(e), ty),
            location: e,
        });
        ty
    }

    fn generate_constraints_inner(&mut self, constraints: &mut ConstraintCtx, e: ExprId) -> TyId {
        let expr = &self.module[e];
        match expr {
            Expr::Missing => self.new_ty_var(),
            Expr::Literal(lit) => {
                let lit: Ty<TyId> = lit.clone().into();
                lit.intern(self)
            }
            Expr::Reference(var_name) => match self.name_res.get(e) {
                None => {
                    // true, false, and null can be shadowed...
                    // so if theres no hit on them return the normal types
                    match var_name.as_str() {
                        "true" | "false" => Ty::Primitive(PrimitiveTy::Bool).intern(self),
                        "null" => Ty::Primitive(PrimitiveTy::Null).intern(self),
                        _ => self.new_ty_var(),
                    }
                }
                Some(res) => match res {
                    &ResolveResult::Definition(name) => self.ty_for_name(name, constraints),
                    ResolveResult::WithExprs(_) => {
                        todo!("handle with exprs in reference gen")
                    }
                    ResolveResult::Builtin(_name) => {
                        todo!("handle builtin exprs in reference gen")
                    }
                },
            },
            Expr::Apply { fun, arg } => {
                let fun_ty = self.generate_constraints(constraints, *fun);
                let arg_ty = self.generate_constraints(constraints, *arg);
                let ret_ty = self.new_ty_var();

                constraints.add(Constraint {
                    kind: RootConstraintKind::Eq(
                        fun_ty,
                        Ty::Lambda {
                            param: arg_ty,
                            body: ret_ty,
                        }
                        .intern(self),
                    ),
                    location: e,
                });

                ret_ty
            }
            Expr::Lambda { param, pat, body } => {
                let param_ty = self.new_ty_var();

                if let Some(name) = *param {
                    let name_ty = self.ty_for_name(name, constraints);
                    constraints.unify_var(e, param_ty, name_ty);
                }

                if let Some(pat) = pat {
                    let mut fields = BTreeMap::new();

                    for &(name, default_expr) in pat.fields.iter() {
                        let default_ty =
                            default_expr.map(|e| self.generate_constraints(constraints, e));
                        let Some(name) = name else { continue };
                        let name_ty = self.ty_for_name(name, constraints);
                        if let Some(default_ty) = default_ty {
                            constraints.unify_var(e, name_ty, default_ty);
                        }
                        let field_text = self.module[name].text.clone();
                        let param_field_ty = self.new_ty_var();
                        constraints.unify_var(e, param_field_ty, name_ty);
                        fields.insert(field_text, param_field_ty);
                    }

                    let rest = pat.ellipsis.then(|| self.new_ty_var());

                    let attr = Ty::AttrSet(AttrSetTy {
                        fields,
                        rest,
                        dyn_ty: None,
                    })
                    .intern(self);

                    constraints.unify_var(e, param_ty, attr);
                }

                let body_ty = self.generate_constraints(constraints, *body);
                Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                }
                .intern(self)
            }
            Expr::BinOp { lhs, rhs, op } => {
                let lhs_ty = self.generate_constraints(constraints, *lhs);
                let rhs_ty = self.generate_constraints(constraints, *rhs);

                // https://nix.dev/manual/nix/2.23/language/operators
                match op {
                    BinOP::Overload(op) => {
                        let ret_ty = self.new_ty_var();

                        constraints.add(Constraint {
                            kind: BinOverloadConstraint {
                                op: *op,
                                lhs: lhs_ty,
                                rhs: rhs_ty,
                                ret_val: ret_ty,
                            }
                            .into(),
                            location: e,
                        });

                        ret_ty
                    }
                    BinOP::Normal(NormalBinOp::Bool(_)) => {
                        let bool_ty = Ty::Primitive(PrimitiveTy::Bool).intern(self);
                        constraints.unify_var(e, lhs_ty, rhs_ty);
                        constraints.unify_var(e, lhs_ty, bool_ty);

                        bool_ty
                    }
                    BinOP::Normal(NormalBinOp::Expr(_)) => {
                        // TODO: should reject function types here if its not an equality check
                        // right now ill allow it but nix will throw an error...
                        // TODO: equality checks actually allow for both sides to be different...
                        constraints.unify_var(e, lhs_ty, rhs_ty);

                        Ty::Primitive(PrimitiveTy::Bool).intern(self)
                    }
                    BinOP::Normal(NormalBinOp::ListConcat) => {
                        let list_elem_ty = self.new_ty_var();
                        let list_ty = Ty::List(list_elem_ty).intern(self);
                        constraints.unify_var(e, lhs_ty, rhs_ty);
                        constraints.unify_var(e, lhs_ty, list_ty);

                        list_ty
                    }
                    BinOP::Normal(NormalBinOp::AttrUpdate) => {
                        let ret_ty = self.new_ty_var();

                        constraints.add(Constraint {
                            kind: AttrMergeConstraint {
                                lhs: lhs_ty,
                                rhs: rhs_ty,
                                ret_val: ret_ty,
                            }
                            .into(),
                            location: e,
                        });

                        ret_ty
                    }
                }
            }
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                let cond_ty = self.generate_constraints(constraints, *cond);

                constraints.add(Constraint {
                    kind: RootConstraintKind::Eq(
                        cond_ty,
                        Ty::Primitive(PrimitiveTy::Bool).intern(self),
                    ),
                    location: e,
                });

                let then_ty = self.generate_constraints(constraints, *then_body);
                let else_ty = self.generate_constraints(constraints, *else_body);

                constraints.add(Constraint {
                    kind: RootConstraintKind::Eq(then_ty, else_ty),
                    location: e,
                });

                then_ty
            }
            Expr::LetIn { bindings, body } => {
                // TODO: we might be doing instantiates twice here
                // once in the gen bind call then in the body
                // maybe in the gen we can fully skip already "evaluated" names?
                self.generate_bind_constraints(constraints, bindings, e);
                self.generate_constraints(constraints, *body)
            }
            Expr::AttrSet {
                is_rec: _,
                bindings,
            } => {
                let attr_ty = self.generate_bind_constraints(constraints, bindings, e);

                Ty::AttrSet(attr_ty).intern(self)
            }
            Expr::Select {
                set,
                attrpath,
                default_expr,
            } => {
                let set_ty = self.generate_constraints(constraints, *set);

                let str_ty: Ty<TyId> = PrimitiveTy::String.into();
                let str_ty = str_ty.intern(self);

                let ret_ty = attrpath.iter().fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.generate_constraints(constraints, attr);
                    constraints.unify_var(e, attr_ty, str_ty);
                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => todo!("Dynamic attr fields not supported yet in select"),
                    };
                    let (attr_with_field, value_ty) = self.attr_with_field(opt_key);
                    // this will make sure the set has the field we asked for
                    constraints.unify_var(e, set_ty, Ty::AttrSet(attr_with_field).intern(self));
                    // returns the value for the field we asked for
                    value_ty
                });
                if let Some(default_expr) = *default_expr {
                    let default_ty = self.generate_constraints(constraints, default_expr);
                    constraints.unify_var(e, ret_ty, default_ty);
                }

                ret_ty
            }

            Expr::List(inner) => {
                let list_elem_ty = self.new_ty_var();
                for elem in inner {
                    let elem_ty = self.generate_constraints(constraints, *elem);
                    constraints.unify_var(*elem, list_elem_ty, elem_ty);
                }

                Ty::List(list_elem_ty).intern(self)
            }
            Expr::UnaryOp { op, expr } => {
                let ty = self.generate_constraints(constraints, *expr);
                match op {
                    rnix::ast::UnaryOpKind::Invert => {
                        let bool_ty = Ty::Primitive(PrimitiveTy::Bool).intern(self);
                        constraints.unify_var(*expr, ty, bool_ty);
                    }
                    rnix::ast::UnaryOpKind::Negate => {
                        constraints.add(Constraint {
                            location: *expr,
                            kind: DeferrableConstraintKind::Negation(ty).into(),
                        });
                    }
                };

                ty
            }

            Expr::HasAttr { set, attrpath: _ } => {
                let set_ty = self.generate_constraints(constraints, *set);

                // TODO: attrpath could be used for narrowing
                let any_attr = Ty::AttrSet(AttrSetTy {
                    fields: BTreeMap::new(),
                    dyn_ty: None,
                    rest: Some(self.new_ty_var()),
                })
                .intern(self);

                constraints.unify_var(*set, set_ty, any_attr);

                set_ty
            }
            Expr::Assert { cond, body } => {
                let cond_ty = self.generate_constraints(constraints, *cond);

                constraints.unify_var(
                    *cond,
                    cond_ty,
                    Ty::Primitive(PrimitiveTy::Bool).intern(self),
                );

                self.generate_constraints(constraints, *body)
            }

            Expr::With { env, body } => todo!("handle with {env:?} {body:?}"),
            Expr::StringInterpolation(_) => todo!(),
            Expr::PathInterpolation(_) => todo!(),
        }
    }

    // makes an attrset with a single field and open rest field to allow for unification later on
    fn attr_with_field(&mut self, field: SmolStr) -> (AttrSetTy<TyId>, TyId) {
        let field_ty = self.new_ty_var();
        let set = AttrSetTy {
            fields: [(field, field_ty)].into_iter().collect(),
            dyn_ty: None,
            rest: Some(self.new_ty_var()),
        };
        (set, field_ty)
    }

    fn generate_bind_constraints(
        &mut self,
        constraints: &mut ConstraintCtx,
        bindings: &Bindings,
        e: ExprId,
    ) -> AttrSetTy<TyId> {
        let _inherit_from_tys = bindings
            .inherit_froms
            .iter()
            .map(|&from_expr| self.generate_constraints(constraints, from_expr))
            .collect::<Vec<_>>();

        let mut fields = BTreeMap::new();
        for &(name, value) in bindings.statics.iter() {
            let name_text = self.module[name].text.clone();
            // if we already have this name in poly_type_env
            // we checked before on a previous SCC group
            // so we can skip generating constraints
            if let Some(ty_schema) = self.poly_type_env.get(&name).cloned() {
                // println!("got poly {ty_schema:?} for name {name:?}");
                let value_ty = self.instantiate(&ty_schema, constraints);
                fields.insert(name_text, value_ty);
                continue;
            }

            let name_ty = self.ty_for_name(name, constraints);
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) | BindingValue::InheritFrom(e) => {
                    self.generate_constraints(constraints, e)
                } // BindingValue::InheritFrom(expr) => {
                  //     // TODO: some duplication with select, might be worth to extract
                  //     let attr_set_ty = inherit_from_tys[i];
                  //     dbg!(self.get_ty(attr_set_ty));
                  //     let (attr_with_field, value_ty) = self.attr_with_field(name_text.clone());
                  //     constraints.unify_var(
                  //         e,
                  //         attr_set_ty,
                  //         Ty::AttrSet(attr_with_field).intern(self),
                  //     );

                  //     value_ty
                  // }
            };
            // TODO: need a good expression look up here
            constraints.unify_var(e, name_ty, value_ty);
            // let generalized_val = self.generalize(value_ty);
            // if self.poly_type_env.contains_key(&name) {
            //     panic!("poly_type_env already has mapping for {name:?}\t {name_text}");
            // }
            // self.poly_type_env.insert(name, generalized_val);
            fields.insert(name_text, value_ty);
        }

        let dyn_ty = (!bindings.dynamics.is_empty()).then(|| {
            todo!()

            // let dyn_ty = self.new_ty_var();
            // for &(k, v) in bindings.dynamics.iter() {
            //     let name_ty = self.infer_expr(k);
            //     self.unify_var_ty(name_ty, Ty::String);
            //     let value_ty = self.infer_expr(v);
            //     self.unify_var(value_ty, dyn_ty);
            // }
            // dyn_ty
        });

        AttrSetTy {
            fields,
            dyn_ty,
            rest: None,
        }
    }
}
