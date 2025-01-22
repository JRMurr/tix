use std::collections::BTreeMap;

use smol_str::SmolStr;

use super::{CheckCtx, Constraint, ConstraintCtx, ConstraintKind, TyId};
use crate::{
    BinOP, BindingValue, Bindings, Expr, ExprId, Literal, NormalBinOp,
    nameres::ResolveResult,
    ty::{AttrSetTy, PrimitiveTy, Ty},
};

impl CheckCtx<'_> {
    pub(super) fn generate_constraints(
        &mut self,
        constraints: &mut ConstraintCtx,
        e: ExprId,
    ) -> TyId {
        let ty = self.generate_constraints_inner(constraints, e);
        constraints.add(Constraint {
            kind: ConstraintKind::Eq(self.ty_for_expr(e), ty),
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
                lit.intern_ty(self)
            }
            Expr::Reference(var_name) => match self.name_res.get(e) {
                None => {
                    // true, false, and null can be shadowed...
                    // so if theres no hit on them return the normal types
                    match var_name.as_str() {
                        "true" | "false" => Ty::Primitive(PrimitiveTy::Bool).intern_ty(self),
                        "null" => Ty::Primitive(PrimitiveTy::Null).intern_ty(self),
                        _ => self.new_ty_var(),
                    }
                }
                Some(res) => match res {
                    &ResolveResult::Definition(name) => self.ty_for_name(name),
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
                    kind: ConstraintKind::Eq(
                        fun_ty,
                        Ty::Lambda {
                            param: arg_ty,
                            body: ret_ty,
                        }
                        .intern_ty(self),
                    ),
                    location: e,
                });

                ret_ty
            }
            Expr::Lambda { param, pat, body } => {
                let param_ty = self.new_ty_var();

                if let Some(name) = *param {
                    let name_ty = self.ty_for_name(name);
                    constraints.unify_var(e, param_ty, name_ty);
                }

                if let Some(pat) = pat {
                    let mut fields = BTreeMap::new();

                    for &(name, default_expr) in pat.fields.iter() {
                        let default_ty =
                            default_expr.map(|e| self.generate_constraints(constraints, e));
                        let Some(name) = name else { continue };
                        let name_ty = self.ty_for_name(name);
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
                    .intern_ty(self);

                    constraints.unify_var(e, param_ty, attr);
                }

                let body_ty = self.generate_constraints(constraints, *body);
                Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                }
                .intern_ty(self)
            }
            Expr::BinOp { lhs, rhs, op } => {
                let lhs_ty = self.generate_constraints(constraints, *lhs);
                let rhs_ty = self.generate_constraints(constraints, *rhs);

                // https://nix.dev/manual/nix/2.23/language/operators
                match op {
                    // TODO: need to handle operator overloading
                    // for now you cant concat strings and adding only works on ints...
                    BinOP::Overload(_) => {
                        constraints.unify_var(e, lhs_ty, rhs_ty);

                        // For now require that they are ints...
                        // could be smarter later...
                        constraints.add(Constraint {
                            kind: ConstraintKind::Eq(
                                lhs_ty,
                                Ty::Primitive(PrimitiveTy::Int).intern_ty(self),
                            ),
                            location: e,
                        });
                        Ty::Primitive(PrimitiveTy::Int).intern_ty(self)
                    }
                    BinOP::Normal(NormalBinOp::Bool(_)) => {
                        let bool_ty = Ty::Primitive(PrimitiveTy::Bool).intern_ty(self);
                        constraints.unify_var(e, lhs_ty, rhs_ty);
                        constraints.unify_var(e, lhs_ty, bool_ty);

                        bool_ty
                    }
                    BinOP::Normal(NormalBinOp::Expr(_)) => {
                        constraints.unify_var(e, lhs_ty, rhs_ty);

                        lhs_ty
                    }
                    BinOP::Normal(NormalBinOp::ListConcat) => {
                        let list_elem_ty = self.new_ty_var();
                        let list_ty = Ty::List(list_elem_ty).intern_ty(self);
                        constraints.unify_var(e, lhs_ty, rhs_ty);
                        constraints.unify_var(e, lhs_ty, list_ty);

                        list_ty
                    }
                    BinOP::Normal(NormalBinOp::AttrUpdate) => {
                        todo!(
                            r#"
                            BinOP::Normal(NormalBinOp::AttrUpdate)
                            need to make sure both sides are attr sets
                            but don't need to care about the fields
                        "#
                        )
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
                    kind: ConstraintKind::Eq(
                        cond_ty,
                        Ty::Primitive(PrimitiveTy::Bool).intern_ty(self),
                    ),
                    location: e,
                });

                let then_ty = self.generate_constraints(constraints, *then_body);
                let else_ty = self.generate_constraints(constraints, *else_body);

                constraints.add(Constraint {
                    kind: ConstraintKind::Eq(then_ty, else_ty),
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

                Ty::AttrSet(attr_ty).intern_ty(self)
            }
            Expr::Select {
                set,
                attrpath,
                default_expr,
            } => {
                let set_ty = self.generate_constraints(constraints, *set);

                // TODO: would be nice to have primitives like this cached
                // is that fine to share?
                let str_ty: Ty<TyId> = PrimitiveTy::String.into();
                let str_ty = str_ty.intern_ty(self);

                let ret_ty = attrpath.iter().fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.generate_constraints(constraints, attr);
                    constraints.unify_var(e, attr_ty, str_ty);
                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => todo!("Dynamic attr fields not supported yet in select"),
                    };
                    let (attr_with_field, value_ty) = self.attr_with_field(opt_key);
                    // this will make sure the set has the field we asked for
                    constraints.unify_var(e, set_ty, Ty::AttrSet(attr_with_field).intern_ty(self));
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

                Ty::List(list_elem_ty).intern_ty(self)
            }
            Expr::UnaryOp { op, expr } => {
                let ty = self.generate_constraints(constraints, *expr);
                let expected_ty = match op {
                    rnix::ast::UnaryOpKind::Invert => {
                        Ty::Primitive(PrimitiveTy::Bool).intern_ty(self)
                    }
                    rnix::ast::UnaryOpKind::Negate => {
                        // TODO: could be a float...
                        Ty::Primitive(PrimitiveTy::Int).intern_ty(self)
                    }
                };
                constraints.unify_var(*expr, ty, expected_ty);
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
                .intern_ty(self);

                constraints.unify_var(*set, set_ty, any_attr);

                set_ty
            }
            Expr::Assert { cond, body } => {
                let cond_ty = self.generate_constraints(constraints, *cond);

                constraints.unify_var(
                    *cond,
                    cond_ty,
                    Ty::Primitive(PrimitiveTy::Bool).intern_ty(self),
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
        // let inherit_from_tys = bindings
        //     .inherit_froms
        //     .iter()
        //     .map(|&from_expr| self.generate_constraints(constraints, from_expr))
        //     .collect::<Vec<_>>();

        let mut fields = BTreeMap::new();
        for &(name, value) in bindings.statics.iter() {
            let name_text = self.module[name].text.clone();
            // if we already have this name in poly_type_env
            // we checked before on a previous SCC group
            // so we can skip generating constraints
            if let Some(ty_schema) = self.poly_type_env.get(&name).cloned() {
                // println!("got poly {ty_schema:?} for name {name:?}");
                let value_ty = self.instantiate(&ty_schema);
                fields.insert(name_text, value_ty);
                continue;
            }

            let name_ty = self.ty_for_name(name);
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) => {
                    self.generate_constraints(constraints, e)
                }
                BindingValue::InheritFrom(i) => {
                    todo!("handle inherit from {i}")
                    // self.infer_set_field(inherit_from_tys[i], Some(name_text.clone()))
                }
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
