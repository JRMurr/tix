use std::collections::{BTreeMap, HashMap};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use crate::{
    BindingValue, Bindings, Expr, ExprId, Module, NameId,
    nameres::{NameResolution, ResolveResult},
};

pub type TyId = Id<Ty>;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Ty {
    Unknown,

    // TODO: could we track literals in the type system like typescript does?
    Null,
    Bool,
    Int,
    Float,
    String,
    Path,
    Uri,

    List(TyId),
    Lambda { param: TyId, body: TyId },
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
struct AttrSetTy {
    // TODO: should be able to have TyId's as keys to handle dynamic keys?
    fields: BTreeMap<SmolStr, TyId>,

    // Merge with fields, this is for all the dynamic fields
    dyn_ty: Option<TyId>,
}

// following inference alg from https://eli.thegreenplace.net/2018/type-inference/
// https://github.com/eliben/code-for-blog/blob/8bdb91bfc007ceef5ba3499502b3ecb67aec3ec7/2018/type-inference/typing.py#L172

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeEquation {
    lhs: TyId,
    rhs: TyId,
    orig_expr: ExprId, // for debugging
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeTable {
    types: Arena<Ty>,

    equations: Vec<TypeEquation>,

    by_name: HashMap<NameId, TyId>,
    by_expr: HashMap<ExprId, TyId>,
}

impl std::ops::Index<TyId> for TypeTable {
    type Output = Ty;
    fn index(&self, index: TyId) -> &Self::Output {
        &self.types[index]
    }
}

// impl std::ops::Index<ExprId> for TypeTable {
//     type Output = TyId;
//     fn index(&self, expr_id: ExprId) -> &Self::Output {
//         self.by_expr
//             .get(&expr_id)
//             .expect("All exprs should have a type mapping")
//     }
// }

impl TypeTable {
    pub fn new(module: &Module, name_res: &NameResolution) -> Self {
        let mut by_name = HashMap::new();
        let mut by_expr = HashMap::new();

        let mut types = Arena::new();

        let equations = Vec::new();

        for (name_id, _) in module.names() {
            let ty_id = types.alloc(Ty::Unknown);
            by_name.insert(name_id, ty_id);
        }

        for (expr_id, _) in module.exprs() {
            let ty_id = match name_res.get(expr_id) {
                Some(ResolveResult::Definition(name_id)) => *by_name.get(name_id).unwrap(),
                _ => types.alloc(Ty::Unknown),
            };
            by_expr.insert(expr_id, ty_id);
        }

        let mut table = Self {
            types,
            by_name,
            by_expr,
            equations,
        };

        table.generate_equations(module, module.entry_expr);

        table
    }

    fn expr_ty(&self, expr_id: &ExprId) -> TyId {
        *self
            .by_expr
            .get(expr_id)
            .expect("All exprs should have a type mapping")
    }

    fn name_ty(&self, name_id: &NameId) -> TyId {
        *self
            .by_name
            .get(name_id)
            .expect("All names should have a type mapping")
    }

    fn generate_equations(&mut self, module: &Module, expr_id: ExprId) {
        let expr_ty = self.expr_ty(&expr_id);

        let expr = &module[expr_id];

        // https://github.com/eliben/code-for-blog/blob/8bdb91bfc007ceef5ba3499502b3ecb67aec3ec7/2018/type-inference/typing.py#L203
        // does the walk before handling the current node.
        // not sure why but ill do the same..
        expr.walk_child_exprs(|e| self.generate_equations(module, e));

        match expr {
            Expr::Reference(_) | Expr::Missing => {
                // do nothing
            }
            // could this be done above to avoid an equation for each literal?
            Expr::Literal(lit) => {
                let lit: Ty = lit.clone().into();
                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: self.types.alloc(lit),
                    orig_expr: expr_id,
                })
            }
            Expr::AttrSet {
                is_rec: _,
                bindings,
            } => {}
            Expr::LetIn { bindings: _, body } => {
                // TODO: can i ignore bindings, name res *should* have handled it?
                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: self.expr_ty(body),
                    orig_expr: expr_id,
                })
            }
            Expr::Apply { fun, arg } => self.equations.push(TypeEquation {
                lhs: self.expr_ty(fun),
                rhs: self.expr_ty(arg),
                orig_expr: expr_id,
            }),
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                self.equations.push(TypeEquation {
                    lhs: self.expr_ty(cond),
                    rhs: self.types.alloc(Ty::Bool),
                    orig_expr: expr_id,
                });
                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: self.expr_ty(then_body),
                    orig_expr: expr_id,
                });
                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: self.expr_ty(else_body),
                    orig_expr: expr_id,
                });
            }
            Expr::Lambda { param, pat, body } => {
                let param_ty = self.types.alloc(Ty::Unknown);

                if let Some(param) = param {
                    self.equations.push(TypeEquation {
                        lhs: self.name_ty(param),
                        rhs: param_ty,
                        orig_expr: expr_id,
                    });
                }

                if let Some(pat) = pat {
                    let mut fields = BTreeMap::new();
                    for &(name, default_expr) in pat.fields.iter() {
                        let Some(name) = name else { continue };
                        let default_ty = default_expr.map(|e| self.expr_ty(&e));

                        let name_ty = self.name_ty(&name);
                        if let Some(default_ty) = default_ty {
                            self.equations.push(TypeEquation {
                                lhs: name_ty,
                                rhs: default_ty,
                                orig_expr: default_expr.unwrap(),
                            })
                        }

                        let field_text = module[name].text.clone();
                        fields.insert(field_text, self.types.alloc(Ty::Unknown));
                    }

                    let attr_set = AttrSetTy {
                        fields,
                        dyn_ty: None,
                    };
                    self.equations.push(TypeEquation {
                        lhs: param_ty,
                        rhs: self.types.alloc(Ty::AttrSet(attr_set)),
                        orig_expr: expr_id,
                    });
                }

                let body_ty = self.expr_ty(body);

                let lam_ty = self.types.alloc(Ty::Lambda {
                    param: param_ty,
                    body: body_ty,
                });

                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: lam_ty,
                    orig_expr: expr_id,
                });
            }
            Expr::List(lst) => {
                let list_elm_ty = self.types.alloc(Ty::Unknown);
                for elem in lst.iter() {
                    self.equations.push(TypeEquation {
                        lhs: list_elm_ty,
                        rhs: self.expr_ty(elem),
                        orig_expr: expr_id,
                    });
                }

                self.equations.push(TypeEquation {
                    lhs: expr_ty,
                    rhs: self.types.alloc(Ty::List(list_elm_ty)),
                    orig_expr: expr_id,
                });
            }
            Expr::BinOp { lhs, rhs, op } => {
                let lhs_ty = self.expr_ty(lhs);
                let rhs_ty = self.expr_ty(rhs);

                // https://nix.dev/manual/nix/2.23/language/operators
                match op {
                    rnix::ast::BinOpKind::Concat => todo!(),
                    rnix::ast::BinOpKind::Update => todo!(),
                    rnix::ast::BinOpKind::Add => todo!(),
                    rnix::ast::BinOpKind::Sub => todo!(),
                    rnix::ast::BinOpKind::Mul => todo!(),
                    rnix::ast::BinOpKind::Div => todo!(),
                    rnix::ast::BinOpKind::And => todo!(),
                    rnix::ast::BinOpKind::Equal => todo!(),
                    rnix::ast::BinOpKind::Implication => todo!(),
                    rnix::ast::BinOpKind::Less => todo!(),
                    rnix::ast::BinOpKind::LessOrEq => todo!(),
                    rnix::ast::BinOpKind::More => todo!(),
                    rnix::ast::BinOpKind::MoreOrEq => todo!(),
                    rnix::ast::BinOpKind::NotEqual => todo!(),
                    rnix::ast::BinOpKind::Or => todo!(),
                }

                todo!()
            }
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
            // e => e.walk_child_exprs(|e| self.generate_equations(module, e)),
        }
    }

    fn gen_bidnings_equations(
        &mut self,
        module: &Module,
        bindings: &Bindings,
        parent_expr: ExprId,
    ) -> AttrSetTy {
        // let _inherit_from_tys = bindings
        //     .inherit_froms
        //     .iter()
        //     .map(|from_expr| self.expr_ty(from_expr))
        //     .collect::<Vec<_>>();

        let mut fields = BTreeMap::new();

        for &(name, value) in bindings.statics.iter() {
            let name_ty = self.name_ty(&name);

            let name_text = module[name].text.clone();
            let value_ty = match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) => self.expr_ty(&e),
                BindingValue::InheritFrom(_) => todo!(), // self.infer_set_field(
                                                         //     inherit_from_tys[i],
                                                         //     Some(name_text.clone()),
                                                         //     AttrSource::Name(name),
                                                         // ),
            };
            self.equations.push(TypeEquation {
                lhs: name_ty,
                rhs: value_ty,
                orig_expr: parent_expr, // TODO: kind of a lie, would be nice to have the expr of the key but this is good enough
            });
            fields.insert(name_text, value_ty);
        }

        AttrSetTy {
            fields,
            dyn_ty: None,
        }
    }

    fn gen_attr_set_field_equations(&mut self, set_ty: TyId, field: Option<SmolStr>) {}

    pub fn update_type(&mut self, id: TyId, new_ty: Ty) {
        let value = self.types.get_mut(id).unwrap();
        *value = new_ty;
    }
}

struct InferCtx {
    module: Module,
    name_res: NameResolution,

    types: TypeTable,
}

impl InferCtx {
    pub fn new(module: Module, name_res: NameResolution) -> Self {
        let types = TypeTable::new(&module, &name_res);

        Self {
            module,
            name_res,
            types,
        }
    }
}
