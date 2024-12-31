mod union_find;

use std::{
    collections::{BTreeMap, HashMap},
    mem,
};

use smol_str::SmolStr;
use union_find::UnionFind;

use crate::{
    ExprId, Module, NameId,
    db::NixFile,
    nameres::NameResolution,
};

/// Reference to the type in the arena
pub type TyId = union_find::UnionIdx<Ty>;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttrSetTy {
    // TODO: should be able to have TyId's as keys to handle dynamic keys?
    fields: BTreeMap<SmolStr, TyId>,

    // Merge with fields, this is for all the dynamic fields
    dyn_ty: Option<TyId>,
}

// following inference alg from https://eli.thegreenplace.net/2018/type-inference/
// https://github.com/eliben/code-for-blog/blob/8bdb91bfc007ceef5ba3499502b3ecb67aec3ec7/2018/type-inference/typing.py#L172

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    lhs: TyId,
    rhs: TyId,
    orig_expr: ExprId, // for debugging
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeTable {
    types: UnionFind<Ty>,

    // constraints: Vec<Constraint>,
    by_name: HashMap<NameId, TyId>,
    by_expr: HashMap<ExprId, TyId>,

    ty_var_count: usize,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferCtx {
    module: Module,
    name_res: NameResolution,

    table: UnionFind<Ty>,
}

impl InferCtx {
    pub fn new(module: Module, name_res: NameResolution) -> Self {
        // let types = TypeTable::new(&module, &name_res);

        let table = UnionFind::new(module.names().len() + module.exprs().len(), |idx| {
            Ty::TyVar(idx.idx())
        });

        // let types = UnionFind::new(len, make_default);
        Self {
            module,
            name_res,
            table,
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

    fn infer_expr(&mut self, e: ExprId) -> TyId {
        let ty = self.infer_expr_inner(e);
        let placeholder_ty = self.ty_for_expr(e);
        self.unify_var(placeholder_ty, ty);
        ty
    }

    fn infer_expr_inner(&mut self, e: ExprId) -> TyId {
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
        todo!()
    }
}

#[salsa::tracked]
pub fn infer_file_debug(db: &dyn crate::Db, file: NixFile) -> InferCtx {
    let module = crate::module(db, file);

    let name_res = crate::nameres::name_resolution(db, file);
    InferCtx::new(module, name_res)
}
