use std::{
    collections::{BTreeMap, HashMap, HashSet},
    mem,
};

use smol_str::SmolStr;
use thiserror::Error;
use union_find::UnionFind;

use crate::{
    BindingValue, Bindings, Expr, ExprId, Literal, Module, NameId,
    db::NixFile,
    nameres::{NameResolution, ResolveResult},
    ty::TyRef,
};

use super::{ArcTy, AttrSetTy, Ty, union_find};

/// Reference to the type in the arena
pub type TyId = union_find::UnionIdx;

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TySchema {
    pub vars: HashSet<usize>, // Each usize corresponds to a Ty::TyVar(x)
    pub ty: TyId,
}

impl Ty<TyId> {
    fn intern(self, ctx: &mut InferCtx) -> TyId {
        ctx.table.push(self)
    }
}

type Substitutions = HashMap<usize, TyId>;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
enum InferenceError {
    #[error("Could not union {0:?} and {1:?}")]
    InvalidUnion(Ty<TyId>, Ty<TyId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: UnionFind<Ty<TyId>>,

    poly_type_env: HashMap<NameId, TySchema>,
}

impl<'db> InferCtx<'db> {
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
        TyId::new(u32::try_from(name.index()).expect("Name id too big"))
    }

    fn ty_for_expr(&self, i: ExprId) -> TyId {
        TyId::new(
            self.module.names().len() as u32 + u32::try_from(i.index()).expect("Expr id too big"),
        )
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
                })
            }
            // TODO: should list them all just incase we add stuff
            rest => rest, // all leaf types
        };

        new_ty.intern(self)
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
            _ => {}
        }

        set
    }

    pub fn infer_expr(&mut self, e: ExprId) -> TyId {
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
                let lit: Ty<TyId> = lit.clone().into();
                lit.intern(self)
            }
            // TODO: I think this will work fine with the type schema.
            // this should be resolved before we make the copy so the name res should work
            // but if stuff gets weird, check here...
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
                    let name_ty = self.ty_for_name(name);
                    self.unify_var(param_ty, name_ty);
                }

                if let Some(pat) = pat {
                    self.unify_var_ty(param_ty, Ty::AttrSet(AttrSetTy::new()));
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
            Expr::LetIn { bindings, body } => {
                self.infer_bindings(bindings);
                self.infer_expr(*body)
            }
            Expr::AttrSet {
                is_rec: _,
                bindings,
            } => {
                let set = self.infer_bindings(bindings);
                Ty::AttrSet(set).intern(self)
            }
            Expr::BinOp { lhs, rhs, op } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);

                // https://nix.dev/manual/nix/2.23/language/operators
                match op {
                    // TODO: need to handle operator overloading or polymorphism here....
                    // for now you cant concat strings and adding only works on ints...
                    rnix::ast::BinOpKind::Add => {
                        self.unify_var(lhs_ty, rhs_ty);

                        // For now require that they are ints...
                        // could be smarter later...
                        let int_ty = Ty::Int.intern(self);
                        self.unify_var(lhs_ty, int_ty);

                        lhs_ty
                    }
                    o => todo!("Need to handle operator {o:?}"),
                }
            }
            Expr::Select {
                set,
                attrpath,
                default_expr,
            } => {
                let set_ty = self.infer_expr(*set);
                let ret_ty = attrpath.iter().fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.infer_expr(attr);
                    self.unify_var_ty(attr_ty, Ty::String);
                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => Some(key.clone()),
                        _ => None,
                    };
                    self.infer_set_field(set_ty, opt_key)
                });
                if let Some(default_expr) = *default_expr {
                    let default_ty = self.infer_expr(default_expr);
                    self.unify_var(ret_ty, default_ty);
                }
                ret_ty
            }
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => todo!(),
            Expr::List(_) => todo!(),
            Expr::UnaryOp { op, expr } => todo!(),

            Expr::HasAttr { set, attrpath } => todo!(),
            Expr::With { env, body } => todo!(),
            Expr::Assert { cond, body } => todo!(),
            Expr::StringInterpolation(_) => todo!(),
            Expr::PathInterpolation(_) => todo!(),
        }
    }

    fn infer_bindings(&mut self, bindings: &Bindings) -> AttrSetTy<TyId> {
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
            // TODO: i feel like i'll need to store the result of generalization on the fields or something..
            // but i think its fine?
            // TODO: i might want to do generlization after all the bindings
            // have been handled if stuff is mutually recursive?
            let generalized_val = self.generalize(value_ty);
            if self.poly_type_env.contains_key(&name) {
                panic!("poly_type_env already has mapping for {name:?}\t {name_text}");
            }
            self.poly_type_env.insert(name, generalized_val);
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

        AttrSetTy { fields, dyn_ty }
    }

    fn infer_set_field(&mut self, set_ty: TyId, field: Option<SmolStr>) -> TyId {
        use std::collections::btree_map::Entry;
        let next_ty = TyId::new(self.table.len() as u32);
        match self.table.get_mut(set_ty) {
            Ty::AttrSet(set) => match field {
                Some(field) => match set.fields.entry(field) {
                    Entry::Occupied(mut ent) => {
                        let ty = ent.get_mut();
                        // prev_src.unify(src);
                        return *ty;
                    }
                    Entry::Vacant(ent) => {
                        ent.insert(next_ty);
                    }
                },
                None => match set.dyn_ty {
                    Some(dyn_ty) => return dyn_ty,
                    None => set.dyn_ty = Some(next_ty),
                },
            },
            k @ Ty::TyVar(_) => {
                *k = Ty::AttrSet(match field {
                    Some(field) => AttrSetTy {
                        fields: [(field, next_ty)].into_iter().collect(),
                        dyn_ty: None,
                    },
                    None => AttrSetTy {
                        fields: BTreeMap::new(),
                        dyn_ty: Some(next_ty),
                    },
                });
            }
            _ => {}
        }
        self.new_ty_var()
    }

    // TODO: When we don't just panic on errors we might want to do the table unify after the type unify call
    fn unify_var_ty(&mut self, var: TyId, rhs: Ty<TyId>) {
        let lhs = mem::replace(self.table.get_mut(var), Ty::TyVar(var.idx()));
        let ret = self.unify(lhs, rhs).expect("Unify error");
        *self.table.get_mut(var) = ret;
    }

    fn unify_var(&mut self, lhs: TyId, rhs: TyId) {
        // dbg!(&lhs, &rhs);
        let (var, rhs) = self.table.unify(lhs, rhs);
        let Some(rhs) = rhs else { return };
        self.unify_var_ty(var, rhs);
    }

    fn unify(&mut self, lhs: Ty<TyId>, rhs: Ty<TyId>) -> Result<Ty<TyId>, InferenceError> {
        if lhs == rhs {
            return Ok(lhs);
        }
        let ty = match (lhs, rhs) {
            // TODO: Don't think i need a contains in check since how i init the type vars should handle that
            // i things are sad will need to do that and error
            (Ty::TyVar(_), other) | (other, Ty::TyVar(_)) => other,
            (Ty::List(a), Ty::List(b)) => {
                self.unify_var(a, b);
                Ty::List(a)
            }
            (
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                },
                Ty::Lambda {
                    param: arg2,
                    body: ret2,
                },
            ) => {
                self.unify_var(arg1, arg2);
                self.unify_var(ret1, ret2);
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                }
            }
            // TODO: this might be wack, look into https://bernsteinbear.com/blog/row-poly/
            (Ty::AttrSet(mut a), Ty::AttrSet(b)) => {
                use std::collections::btree_map::Entry;
                for (field, ty2) in b.fields {
                    match a.fields.entry(field) {
                        Entry::Vacant(ent) => {
                            ent.insert(ty2);
                        }
                        Entry::Occupied(mut ent) => {
                            let ty1 = ent.get_mut();
                            // src1.unify(src2);
                            self.unify_var(*ty1, ty2);
                        }
                    }
                }
                Ty::AttrSet(a)
            }
            (l, r) if l == r => l,
            (l, r) => return Err(InferenceError::InvalidUnion(l, r)),
        };

        Ok(ty)
    }

    fn finish(mut self) -> InferenceResult {
        // need to instantiate all names first since it will modify the table
        let name_tys: Vec<_> = self
            .module
            .names()
            .map(|(name, _)| {
                let ty = self.ty_for_name(name);
                (name, ty)
            })
            .collect();

        let expr_tys: Vec<_> = self
            .module
            .exprs()
            .map(|(expr, _)| {
                let ty = self.ty_for_expr(expr);
                (expr, ty)
            })
            .collect();

        let mut i = Collector::new(&mut self.table);

        let name_cnt = self.module.names().len();
        let expr_cnt = self.module.exprs().len();
        let mut name_ty_map = HashMap::with_capacity(name_cnt);
        let mut expr_ty_map = HashMap::with_capacity(expr_cnt);
        for (name, ty) in name_tys {
            name_ty_map.insert(name, i.collect(ty));
        }
        for (expr, ty) in expr_tys {
            expr_ty_map.insert(expr, i.collect(ty));
        }

        InferenceResult {
            name_ty_map,
            expr_ty_map,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    name_ty_map: HashMap<NameId, ArcTy>,
    expr_ty_map: HashMap<ExprId, ArcTy>,
}

impl InferenceResult {
    pub fn ty_for_name(&self, name: NameId) -> ArcTy {
        self.name_ty_map.get(&name).unwrap().clone()
    }

    pub fn ty_for_expr(&self, expr: ExprId) -> ArcTy {
        self.expr_ty_map.get(&expr).unwrap().clone()
    }
}

/// Traverse the table and freeze all `Ty`s into immutable ones.
struct Collector<'a> {
    cache: HashMap<TyId, ArcTy>,
    table: &'a mut UnionFind<Ty<TyId>>,
}

impl<'a> Collector<'a> {
    fn new(table: &'a mut UnionFind<Ty<TyId>>) -> Self {
        Self {
            cache: HashMap::with_capacity(table.len()),
            table,
        }
    }

    fn collect(&mut self, ty: TyId) -> ArcTy {
        let i = self.table.find(ty);
        if let Some(ty) = self.cache.get(&i).cloned() {
            return ty;
        }

        let ret = self.collect_uncached(ty);
        self.cache.insert(i, ret.clone());
        ret
    }

    fn collect_uncached(&mut self, i: TyId) -> ArcTy {
        // TODO: not sure if we need to worry about cycles
        // I think it should be fine? If so worth trying Arc::new_cyclic to handle it?
        let ty = self.table.get_mut(i).clone();
        match ty {
            Ty::TyVar(x) => ArcTy::TyVar(x),
            Ty::Null => ArcTy::Null,
            Ty::Uri => ArcTy::Uri,
            Ty::Bool => ArcTy::Bool,
            Ty::Int => ArcTy::Int,
            Ty::Float => ArcTy::Float,
            Ty::String => ArcTy::String,
            Ty::Path => ArcTy::Path,
            Ty::List(a) => ArcTy::List(self.collect(a).into()),
            Ty::Lambda { param, body } => {
                let param = self.collect(param).into();
                let body = self.collect(body).into();
                ArcTy::Lambda { param, body }
            }
            Ty::AttrSet(fields) => {
                let fields = fields
                    .fields
                    .into_iter()
                    .map(|(name, ty)| {
                        let ty_ref: TyRef = self.collect(ty).into();
                        (name, ty_ref)
                    })
                    .collect();
                Ty::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty: None,
                })
            }
        }
    }
}

#[salsa::tracked]
pub fn infer_file_debug(db: &dyn crate::Db, file: NixFile) -> InferenceResult {
    let module = crate::module(db, file);

    let name_res = crate::nameres::name_resolution(db, file);
    let mut infer = InferCtx::new(&module, &name_res);

    infer.infer_expr(module.entry_expr);

    infer.finish()
}
