// TODO: this should replace infer.rs

use std::collections::{BTreeMap, HashMap, HashSet};

use smol_str::SmolStr;

use crate::{
    BindingValue, Bindings, Expr, ExprId, Literal, Module, NameId,
    nameres::{NameResolution, ResolveResult},
};

use super::{
    AttrSetTy, PrimitiveTy, Ty,
    union_find::{self, UnionFind},
};

/// Reference to the type in the arena
pub type TyId = union_find::UnionIdx;

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TySchema {
    pub vars: HashSet<usize>, // Each usize corresponds to a Ty::TyVar(x)
    pub ty: TyId,
}

impl Ty<TyId> {
    fn intern_ty(self, ctx: &mut CheckCtx) -> TyId {
        ctx.table.push(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint {
    kind: ConstraintKind,
    location: ExprId,
}

#[derive(Debug, PartialEq, Eq, Clone)]

pub enum TyRef {
    Id(TyId),      // unification var
    Ref(Ty<TyId>), // a type
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintKind {
    Eq(TyId, TyRef),
}

type Substitutions = HashMap<usize, TyId>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: UnionFind<Ty<TyId>>,

    poly_type_env: HashMap<NameId, TySchema>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintCtx {
    constraints: Vec<Constraint>,
}

impl ConstraintCtx {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    pub fn add(&mut self, c: Constraint) {
        self.constraints.push(c);
    }

    pub fn unify_var(&mut self, e: ExprId, lhs: TyId, rhs: TyId) {
        self.constraints.push(Constraint {
            location: e,
            kind: ConstraintKind::Eq(lhs, TyRef::Id(rhs)),
        });
    }

    pub fn unify_var_ty(&mut self, e: ExprId, lhs: TyId, rhs: Ty<TyId>) {
        self.constraints.push(Constraint {
            location: e,
            kind: ConstraintKind::Eq(lhs, TyRef::Ref(rhs)),
        });
    }
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        // let types = TypeTable::new(&module, &name_res);

        // Init the table with placeholder types for all names and expressions
        // adding names here allows for recursive references
        // After we infer a name's value it should be added to the poly_type_env
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

    fn ty_for_name(&mut self, name: NameId) -> TyId {
        let ty_schema = self.poly_type_env.get(&name).cloned();

        if let Some(ty_schema) = ty_schema {
            return self.instantiate(&ty_schema);
        }

        // NOTE: this should only happen during the inference of the value for the name
        // after inferring we should add the name to the poly type env
        TyId::new(u32::from(name.into_raw()))
    }

    fn ty_for_expr(&self, i: ExprId) -> TyId {
        TyId::new(self.module.names().len() as u32 + u32::from(i.into_raw()))
    }

    fn instantiate(&mut self, scheme: &TySchema) -> TyId {
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
                    rest: None,
                })
            }
            Ty::Primitive(_) => ty,
        };

        new_ty.intern_ty(self)
    }

    fn generalize(&mut self, ty: TyId) -> TySchema {
        let free_vars = self.free_type_vars(ty);
        TySchema {
            vars: free_vars,
            ty,
        }
    }

    fn free_type_vars(&mut self, ty_id: TyId) -> HashSet<usize> {
        let ty = self.table.get_mut(ty_id).clone();

        let mut set = HashSet::new();

        match ty {
            Ty::TyVar(x) => {
                set.insert(x);
            }
            Ty::List(inner) => set.extend(&self.free_type_vars(inner)),
            Ty::Lambda { param, body } => {
                set.extend(&self.free_type_vars(param));
                set.extend(&self.free_type_vars(body));
            }
            Ty::AttrSet(attr_set_ty) => {
                attr_set_ty.fields.values().for_each(|v| {
                    set.extend(&self.free_type_vars(*v));
                });

                if let Some(dyn_ty) = attr_set_ty.dyn_ty {
                    set.extend(&self.free_type_vars(dyn_ty));
                }
            }
            Ty::Primitive(_) => {}
        }

        set
    }

    fn generate_constraints(&mut self, constraints: &mut ConstraintCtx, e: ExprId) -> TyId {
        let expr = &self.module[e];
        match expr {
            Expr::Missing => self.new_ty_var(),
            Expr::Literal(lit) => {
                let lit: Ty<TyId> = lit.clone().into();
                lit.intern_ty(self)
            }
            Expr::Reference(_) => match self.name_res.get(e) {
                None => self.new_ty_var(),
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
                        TyRef::Ref(Ty::Lambda {
                            param: arg_ty,
                            body: ret_ty,
                        }),
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

                if let Some(_pat) = pat {
                    todo!("generate constrains for lambda pattern")
                    // self.unify_var_ty(param_ty, Ty::AttrSet(AttrSetTy::new()));
                    // for &(name, default_expr) in pat.fields.iter() {
                    //     // Always infer default_expr.
                    //     let default_ty = default_expr.map(|e| self.infer_expr(e));
                    //     let Some(name) = name else { continue };
                    //     let name_ty = self.ty_for_name(name);
                    //     if let Some(default_ty) = default_ty {
                    //         self.unify_var(name_ty, default_ty);
                    //     }
                    //     let field_text = self.module[name].text.clone();
                    //     let param_field_ty = self.infer_set_field(param_ty, Some(field_text));
                    //     self.unify_var(param_field_ty, name_ty);
                    // }
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
                    // TODO: need to handle operator overloading or polymorphism here....
                    // for now you cant concat strings and adding only works on ints...
                    rnix::ast::BinOpKind::Add => {
                        constraints.unify_var(e, lhs_ty, rhs_ty);

                        // For now require that they are ints...
                        // could be smarter later...
                        constraints.add(Constraint {
                            kind: ConstraintKind::Eq(
                                lhs_ty,
                                TyRef::Ref(Ty::Primitive(PrimitiveTy::Int)),
                            ),
                            location: e,
                        });
                        lhs_ty
                    }
                    o => todo!("Need to handle operator {o:?}"),
                }
            }
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => todo!("gen if then else"),
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
                let ret_ty = attrpath.iter().fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.generate_constraints(constraints, attr);
                    constraints.unify_var_ty(e, attr_ty, PrimitiveTy::String.into());
                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => todo!("Dyanmic attr fields not supported yet in select"),
                    };
                    let (attr_with_field, value_ty) = self.attr_with_field(opt_key);
                    // this will make sure the set has the field we asked for
                    constraints.unify_var_ty(e, set_ty, Ty::AttrSet(attr_with_field));
                    // returns the value for the field we asked for
                    value_ty
                });
                if let Some(default_expr) = *default_expr {
                    let default_ty = self.generate_constraints(constraints, default_expr);
                    constraints.unify_var(e, ret_ty, default_ty);
                }

                ret_ty
            }

            Expr::List(_) => todo!(),
            Expr::UnaryOp { op, expr } => todo!(),

            Expr::HasAttr { set, attrpath } => todo!(),
            Expr::With { env, body } => todo!(),
            Expr::Assert { cond, body } => todo!(),
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
