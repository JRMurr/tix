mod union_find;

use std::{
    collections::{BTreeMap, HashMap},
    mem,
};

use smol_str::SmolStr;
use union_find::UnionFind;

use crate::{
    BindingValue, Bindings, Expr, ExprId, Module, NameId,
    db::NixFile,
    nameres::{NameResolution, ResolveResult},
};

/// Reference to the type in the arena
pub type TyId = union_find::UnionIdx<Ty>;

// the mono type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// A type quantifier (ie the `a` in `a -> a`)
    TyVar(usize),

    // TODO: could we track literals in the type system like typescript does?
    Null,
    Bool,
    Int,
    Float,
    String,
    Path,
    Uri,

    List(TyId),
    Lambda {
        param: TyId,
        body: TyId,
    },
    AttrSet(AttrSetTy),
}

impl Ty {
    fn intern(self, ctx: &mut InferCtx) -> TyId {
        ctx.table.push(self)
    }
}

impl From<crate::Literal> for Ty {
    fn from(value: crate::Literal) -> Self {
        match value {
            crate::Literal::Float(_) => Ty::Float,
            crate::Literal::Integer(_) => Ty::Int,
            crate::Literal::String(_) => Ty::String,
            crate::Literal::Path(_) => Ty::Path,
            crate::Literal::Uri => Ty::Uri,
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct AttrSetTy {
    // TODO: should be able to have TyId's as keys to handle dynamic keys?
    fields: BTreeMap<SmolStr, TyId>,

    // Merge with fields, this is for all the dynamic fields
    dyn_ty: Option<TyId>,
}

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyScheme {
    pub vars: Vec<usize>, // Each usize corresponds to a Ty::TyVar(x)
    pub ty: TyId,
}

// impl std::ops::Index<TyId> for TypeTable {
//     type Output = Ty;
//     fn index(&self, index: TyId) -> &Self::Output {
//         &self.types[index]
//     }
// }

// impl std::ops::Index<ExprId> for TypeTable {
//     type Output = TyId;
//     fn index(&self, expr_id: ExprId) -> &Self::Output {
//         self.by_expr
//             .get(&expr_id)
//             .expect("All exprs should have a type mapping")
//     }
// }

// impl TypeTable {
//     pub fn new(module: &Module, name_res: &NameResolution) -> Self {
//         let mut by_name = HashMap::new();
//         let mut by_expr = HashMap::new();

//         let mut types = Arena::new();

//         // let constraints = Vec::new();

//         // for (name_id, _) in module.names() {
//         //     let ty_id = types.alloc(Ty::Unknown);
//         //     by_name.insert(name_id, ty_id);
//         // }

//         // for (expr_id, _) in module.exprs() {
//         //     let ty_id = match name_res.get(expr_id) {
//         //         Some(ResolveResult::Definition(name_id)) => *by_name.get(name_id).unwrap(),
//         //         _ => types.alloc(Ty::Unknown),
//         //     };
//         //     by_expr.insert(expr_id, ty_id);
//         // }

//         Self {
//             types,
//             by_name,
//             by_expr,
//             ty_var_count: 0, // constraints,
//         }

//         // let mut table = Self {
//         //     types,
//         //     by_name,
//         //     by_expr,
//         //     ty_var_count: 0, // constraints,
//         // };

//         // table.generate_constraints(module, module.entry_expr);

//         // table
//     }

//     fn expr_ty(&self, expr_id: &ExprId) -> TyId {
//         *self
//             .by_expr
//             .get(expr_id)
//             .expect("All exprs should have a type mapping")
//     }

//     fn name_ty(&self, name_id: &NameId) -> TyId {
//         *self
//             .by_name
//             .get(name_id)
//             .expect("All names should have a type mapping")
//     }

//     fn generate_constraints(&mut self, module: &Module, expr_id: ExprId) {
//         let expr_ty = self.expr_ty(&expr_id);

//         let expr = &module[expr_id];

//         // https://github.com/eliben/code-for-blog/blob/8bdb91bfc007ceef5ba3499502b3ecb67aec3ec7/2018/type-inference/typing.py#L203
//         // does the walk before handling the current node.
//         // not sure why but ill do the same..
//         expr.walk_child_exprs(|e| self.generate_constraints(module, e));

//         match expr {
//             Expr::Reference(_) | Expr::Missing => {
//                 // do nothing
//             }
//             // could this be done above to avoid a constraint for each literal?
//             Expr::Literal(lit) => {
//                 let lit: Ty = lit.clone().into();
//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.types.alloc(lit),
//                     orig_expr: expr_id,
//                 })
//             }
//             Expr::AttrSet {
//                 is_rec: _,
//                 bindings,
//             } => {
//                 let attr_set = self.generate_bindings_constraints(module, bindings, expr_id);

//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.types.alloc(Ty::AttrSet(attr_set)),
//                     orig_expr: expr_id,
//                 });
//             }
//             Expr::LetIn { bindings: _, body } => {
//                 // TODO: can i ignore bindings, name res *should* have handled it?
//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.expr_ty(body),
//                     orig_expr: expr_id,
//                 })
//             }
//             Expr::Apply { fun, arg } => self.constraints.push(Constraint {
//                 lhs: self.expr_ty(fun),
//                 rhs: self.expr_ty(arg),
//                 orig_expr: expr_id,
//             }),
//             Expr::IfThenElse {
//                 cond,
//                 then_body,
//                 else_body,
//             } => {
//                 self.constraints.push(Constraint {
//                     lhs: self.expr_ty(cond),
//                     rhs: self.types.alloc(Ty::Bool),
//                     orig_expr: expr_id,
//                 });
//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.expr_ty(then_body),
//                     orig_expr: expr_id,
//                 });
//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.expr_ty(else_body),
//                     orig_expr: expr_id,
//                 });
//             }
//             Expr::Lambda { param, pat, body } => {
//                 let param_ty = self.types.alloc(Ty::Unknown);

//                 if let Some(param) = param {
//                     self.constraints.push(Constraint {
//                         lhs: self.name_ty(param),
//                         rhs: param_ty,
//                         orig_expr: expr_id,
//                     });
//                 }

//                 if let Some(pat) = pat {
//                     let mut fields = BTreeMap::new();
//                     for &(name, default_expr) in pat.fields.iter() {
//                         let Some(name) = name else { continue };
//                         let default_ty = default_expr.map(|e| self.expr_ty(&e));

//                         let name_ty = self.name_ty(&name);
//                         if let Some(default_ty) = default_ty {
//                             self.constraints.push(Constraint {
//                                 lhs: name_ty,
//                                 rhs: default_ty,
//                                 orig_expr: default_expr.unwrap(),
//                             })
//                         }

//                         let field_text = module[name].text.clone();
//                         fields.insert(field_text, self.types.alloc(Ty::Unknown));
//                     }

//                     let attr_set = AttrSetTy {
//                         fields,
//                         dyn_ty: None,
//                     };
//                     self.constraints.push(Constraint {
//                         lhs: param_ty,
//                         rhs: self.types.alloc(Ty::AttrSet(attr_set)),
//                         orig_expr: expr_id,
//                     });
//                 }

//                 let body_ty = self.expr_ty(body);

//                 let lam_ty = self.types.alloc(Ty::Lambda {
//                     param: param_ty,
//                     body: body_ty,
//                 });

//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: lam_ty,
//                     orig_expr: expr_id,
//                 });
//             }
//             Expr::List(lst) => {
//                 let list_elm_ty = self.types.alloc(Ty::Unknown);
//                 for elem in lst.iter() {
//                     self.constraints.push(Constraint {
//                         lhs: list_elm_ty,
//                         rhs: self.expr_ty(elem),
//                         orig_expr: expr_id,
//                     });
//                 }

//                 self.constraints.push(Constraint {
//                     lhs: expr_ty,
//                     rhs: self.types.alloc(Ty::List(list_elm_ty)),
//                     orig_expr: expr_id,
//                 });
//             }
//             Expr::BinOp { lhs, rhs, op } => {
//                 let lhs_ty = self.expr_ty(lhs);
//                 let rhs_ty = self.expr_ty(rhs);

//                 // https://nix.dev/manual/nix/2.23/language/operators
//                 match op {
//                     // TODO: need to handle operator overloading or polymorphism here....
//                     // for now you cant concat strings and adding only works on ints...
//                     rnix::ast::BinOpKind::Add => {
//                         // force sides are equal (will need to remove once we allow mixing types on both sides)
//                         self.constraints.push(Constraint {
//                             lhs: lhs_ty,
//                             rhs: rhs_ty,
//                             orig_expr: expr_id,
//                         });

//                         // they should both be numbers (for now)
//                         self.constraints.push(Constraint {
//                             lhs: lhs_ty,
//                             rhs: self.types.alloc(Ty::Int),
//                             orig_expr: expr_id,
//                         });

//                         self.constraints.push(Constraint {
//                             lhs: rhs_ty,
//                             rhs: self.types.alloc(Ty::Int),
//                             orig_expr: expr_id,
//                         });
//                     }
//                     o => todo!("Need to handle operator {o:?}"),
//                 }
//             }
//             Expr::Select {
//                 set,
//                 attrpath,
//                 default_expr,
//             } => {
//                 let set_ty = self.expr_ty(set);

//                 let ret_t = attrpath.iter().fold(set_ty, |set_ty, attr| {
//                     let attr_ty = self.expr_ty(attr);
//                     self.constraints.push(Constraint {
//                         lhs: attr_ty,
//                         rhs: self.types.alloc(Ty::String),
//                         orig_expr: expr_id,
//                     });
//                     todo!();
//                 });

//                 todo!();
//             }
//             Expr::UnaryOp { op, expr } => todo!(),
//             Expr::HasAttr { set, attrpath } => todo!(),
//             Expr::With { env, body } => todo!(),
//             Expr::Assert { cond, body } => todo!(),
//             Expr::StringInterpolation(_) => todo!(),
//             Expr::PathInterpolation(_) => todo!(),
//         }
//     }

//     fn generate_bindings_constraints(
//         &mut self,
//         module: &Module,
//         bindings: &Bindings,
//         parent_expr: ExprId,
//     ) -> AttrSetTy {
//         // let _inherit_from_tys = bindings
//         //     .inherit_froms
//         //     .iter()
//         //     .map(|from_expr| self.expr_ty(from_expr))
//         //     .collect::<Vec<_>>();

//         let mut fields = BTreeMap::new();

//         for &(name, value) in bindings.statics.iter() {
//             let name_ty = self.name_ty(&name);

//             let name_text = module[name].text.clone();
//             let value_ty = match value {
//                 BindingValue::Inherit(e) | BindingValue::Expr(e) => self.expr_ty(&e),
//                 BindingValue::InheritFrom(_) => todo!(), // self.infer_set_field(
//                                                          //     inherit_from_tys[i],
//                                                          //     Some(name_text.clone()),
//                                                          //     AttrSource::Name(name),
//                                                          // ),
//             };
//             self.constraints.push(Constraint {
//                 lhs: name_ty,
//                 rhs: value_ty,
//                 orig_expr: parent_expr, // TODO: kind of a lie, would be nice to have the expr of the key but this is good enough
//             });
//             fields.insert(name_text, value_ty);
//         }

//         AttrSetTy {
//             fields,
//             dyn_ty: None,
//         }
//     }

//     pub fn update_type(&mut self, id: TyId, new_ty: Ty) {
//         let value = self.types.get_mut(id).unwrap();
//         *value = new_ty;
//     }

//     // pub fn tys_for_constraint(&self, constraint: Constraint) -> (Ty, Ty) {
//     //     let lhs = constraint.lhs;
//     //     let rhs = constraint.rhs;

//     //     (
//     //         self.types[constraint.lhs].clone(),
//     //         self.types[constraint.rhs].clone(),
//     //     )
//     // }
// }

type Substitutions = HashMap<usize, TyId>;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: UnionFind<Ty>,

    poly_type_env: HashMap<NameId, TyScheme>,
}

impl<'db> InferCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        // let types = TypeTable::new(&module, &name_res);

        let table = UnionFind::new(module.names().len() + module.exprs().len(), |idx| {
            Ty::TyVar(idx.idx())
        });

        // let types = UnionFind::new(len, make_default);
        Self {
            module,
            name_res,
            table,
            poly_type_env: HashMap::new(),
        }
    }

    fn new_ty_var(&mut self) -> TyId {
        self.table.push_with_idx(|idx| Ty::TyVar(idx.idx()))
    }

    fn ty_for_name(&self, i: NameId) -> TyId {
        TyId::new(u32::try_from(i.index()).expect("Name id too big"))
    }

    fn ty_for_expr(&self, i: ExprId) -> TyId {
        TyId::new(
            self.module.names().len() as u32 + u32::try_from(i.index()).expect("Expr id too big"),
        )
    }

    fn instantiate(&mut self, scheme: &TyScheme) -> TyId {
        let mut substitutions = HashMap::new();
        for &var in &scheme.vars {
            substitutions.insert(var, self.new_ty_var());
        }

        self.instantiate_ty(scheme.ty, &substitutions)
    }

    fn instantiate_ty(&mut self, ty_id: TyId, substitutions: &Substitutions) -> TyId {
        let ty = self.table.get_mut(ty_id).clone();

        let new_ty = match ty {
            Ty::TyVar(x) => {
                if let Some(&replacement) = substitutions.get(&x) {
                    return replacement;
                }
                // this should have been unified by now...
                panic!("No substitution found for Ty::TyVar({x})")
            }
            Ty::Lambda { param, body } => {
                let new_param = self.instantiate_ty(param, substitutions);
                let new_body = self.instantiate_ty(body, substitutions);
                Ty::Lambda {
                    param: new_param,
                    body: new_body,
                }
            }
            Ty::List(inner) => {
                let new_inner = self.instantiate_ty(inner, substitutions);
                Ty::List(new_inner)
            }
            Ty::AttrSet(attr_set_ty) => {
                let new_fields = attr_set_ty
                    .fields
                    .into_iter()
                    .map(|(k, v)| (k, self.instantiate_ty(v, substitutions)))
                    .collect();
                let new_dyn_ty = attr_set_ty
                    .dyn_ty
                    .map(|v| self.instantiate_ty(v, substitutions));

                Ty::AttrSet(AttrSetTy {
                    fields: new_fields,
                    dyn_ty: new_dyn_ty,
                })
            }
            // TODO: should list them all just incase we add stuff
            rest => rest, // all leaf types
        };

        new_ty.intern(self)
    }

    fn infer_expr(&mut self, e: ExprId) -> TyId {
        let ty = self.infer_expr_inner(e);
        let placeholder_ty = self.ty_for_expr(e);
        self.unify_var(placeholder_ty, ty);
        ty
    }

    fn infer_expr_inner(&mut self, e: ExprId) -> TyId {
        let expr = &self.module[e];
        match expr {
            Expr::Missing => self.new_ty_var(),
            Expr::Literal(lit) => {
                let lit: Ty = lit.clone().into();
                lit.intern(self)
            }
            Expr::Reference(_) => match self.name_res.get(e) {
                None => self.new_ty_var(),
                Some(res) => match res {
                    &ResolveResult::Definition(name) => self.ty_for_name(name),
                    ResolveResult::WithExprs(_) => {
                        // TODO: With names.
                        self.new_ty_var()
                    }
                    ResolveResult::Builtin(_name) => {
                        todo!()
                    }
                },
            },
            Expr::Lambda { param, pat, body } => {
                let param_ty = self.new_ty_var();

                if let Some(name) = *param {
                    self.unify_var(param_ty, self.ty_for_name(name));
                }

                if let Some(pat) = pat {
                    self.unify_var_ty(param_ty, Ty::AttrSet(AttrSetTy::default()));
                    for &(name, default_expr) in pat.fields.iter() {
                        // Always infer default_expr.
                        let default_ty = default_expr.map(|e| self.infer_expr(e));
                        let Some(name) = name else { continue };
                        let name_ty = self.ty_for_name(name);
                        if let Some(default_ty) = default_ty {
                            self.unify_var(name_ty, default_ty);
                        }
                        let field_text = self.module[name].text.clone();
                        let param_field_ty = self.infer_set_field(param_ty, Some(field_text));
                        self.unify_var(param_field_ty, name_ty);
                    }
                }

                let body_ty = self.infer_expr(*body);
                Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                }
                .intern(self)
            }
            Expr::Apply { fun, arg } => {
                let param_ty = self.new_ty_var();
                let ret_ty = self.new_ty_var();
                let lam_ty = self.infer_expr(*fun);
                self.unify_var_ty(lam_ty, Ty::Lambda {
                    param: param_ty,
                    body: ret_ty,
                });
                let arg_ty = self.infer_expr(*arg);
                self.unify_var(arg_ty, param_ty);
                ret_ty
            }
            Expr::AttrSet {
                is_rec: _,
                bindings,
            } => {
                let set = self.infer_bindings(bindings);
                Ty::AttrSet(set).intern(self)
            }
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => todo!(),
            Expr::LetIn { bindings, body } => todo!(),
            Expr::List(_) => todo!(),
            Expr::BinOp { lhs, rhs, op } => todo!(),
            Expr::UnaryOp { op, expr } => todo!(),
            Expr::Select {
                set,
                attrpath,
                default_expr,
            } => todo!(),
            Expr::HasAttr { set, attrpath } => todo!(),
            Expr::With { env, body } => todo!(),
            Expr::Assert { cond, body } => todo!(),
            Expr::StringInterpolation(_) => todo!(),
            Expr::PathInterpolation(_) => todo!(),
        }
    }

    fn infer_bindings(&mut self, bindings: &Bindings) -> AttrSetTy {
        let inherit_from_tys = bindings
            .inherit_froms
            .iter()
            .map(|&from_expr| self.infer_expr(from_expr))
            .collect::<Vec<_>>();

        let mut fields = BTreeMap::new();
        for &(name, value) in bindings.statics.iter() {
            let name_ty = self.ty_for_name(name);
            let name_text = self.module[name].text.clone();
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) => self.infer_expr(e),
                BindingValue::InheritFrom(i) => {
                    self.infer_set_field(inherit_from_tys[i], Some(name_text.clone()))
                }
            };
            self.unify_var(name_ty, value_ty);
            fields.insert(name_text, value_ty);
        }

        let dyn_ty = (!bindings.dynamics.is_empty()).then(|| {
            let dyn_ty = self.new_ty_var();
            for &(k, v) in bindings.dynamics.iter() {
                let name_ty = self.infer_expr(k);
                self.unify_var_ty(name_ty, Ty::String);
                let value_ty = self.infer_expr(v);
                self.unify_var(value_ty, dyn_ty);
            }
            dyn_ty
        });

        AttrSetTy { fields, dyn_ty }
    }

    fn infer_set_field(&mut self, set_ty: TyId, field: Option<SmolStr>) -> TyId {
        todo!()
    }

    fn unify_var_ty(&mut self, var: TyId, rhs: Ty) {
        let lhs = mem::replace(self.table.get_mut(var), Ty::TyVar(var.idx()));
        let ret = self.unify(lhs, rhs);
        *self.table.get_mut(var) = ret;
    }

    fn unify_var(&mut self, lhs: TyId, rhs: TyId) {
        let (var, rhs) = self.table.unify(lhs, rhs);
        let Some(rhs) = rhs else { return };
        self.unify_var_ty(var, rhs);
    }

    fn unify(&mut self, lhs: Ty, rhs: Ty) -> Ty {
        if lhs == rhs {
            return lhs;
        }

        match (lhs, rhs) {
            (Ty::TyVar(x), Ty::TyVar(y)) => {
                if x == y {
                    lhs
                } else {
                    panic!("TODO: invalid unification")
                }
            }
            _ => todo!(),
        }
    }

    // fn finish(mut self) -> InferenceResult {
    //     let mut i = Collector::new(&mut self.table);

    //     let name_cnt = self.module.names().len();
    //     let expr_cnt = self.module.exprs().len();
    //     let mut name_ty_map = ArenaMap::with_capacity(name_cnt);
    //     let mut expr_ty_map = ArenaMap::with_capacity(expr_cnt);
    //     for (name, _) in self.module.names() {
    //         let ty = TyVar(u32::from(name.into_raw()));
    //         name_ty_map.insert(name, i.collect(ty));
    //     }
    //     for (expr, _) in self.module.exprs() {
    //         let ty = TyVar(name_cnt as u32 + u32::from(expr.into_raw()));
    //         expr_ty_map.insert(expr, i.collect(ty));
    //     }

    //     InferenceResult {
    //         name_ty_map,
    //         expr_ty_map,
    //     }
    // }
}

#[salsa::tracked]
pub fn infer_file_debug(db: &dyn crate::Db, file: NixFile) -> UnionFind<Ty> {
    let module = crate::module(db, file);

    let name_res = crate::nameres::name_resolution(db, file);
    let infer = InferCtx::new(&module, &name_res);

    infer.table
}
