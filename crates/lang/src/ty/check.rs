// TODO: this should replace infer.rs

use std::collections::{BTreeMap, HashMap, HashSet};

use ena::unify::{self, InPlaceUnificationTable, UnifyKey, UnifyValue};
use la_arena::{Arena, Idx as Id, RawIdx};
use smol_str::SmolStr;
use thiserror::Error;

use crate::{
    BindingValue, Bindings, Expr, ExprId, Literal, Module, NameId,
    db::NixFile,
    nameres::{DependentGroup, GroupedDefs, NameResolution, ResolveResult},
};

use super::{ArcTy, AttrSetTy, PrimitiveTy, Ty};

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct TyId(Id<Ty<TyId>>);

impl From<u32> for TyId {
    #[inline]
    fn from(value: u32) -> Self {
        let id: RawIdx = value.into();
        Self(Id::from_raw(id))
    }
}

impl From<usize> for TyId {
    #[inline]
    fn from(value: usize) -> Self {
        (value as u32).into()
    }
}

pub type Types = Arena<Ty<TyId>>;

impl From<Id<Ty<TyId>>> for TyId {
    fn from(value: Id<Ty<TyId>>) -> Self {
        Self(value)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TyIdEqKey {
    id: TyId,
}

impl From<TyId> for TyIdEqKey {
    #[inline]
    fn from(value: TyId) -> Self {
        Self { id: value }
    }
}

#[derive(Clone, Debug)]
pub enum TypeVariableValue {
    Known(TyId),
    Unknown,
}

impl UnifyKey for TyIdEqKey {
    type Value = TypeVariableValue;

    fn index(&self) -> u32 {
        self.id.0.into_raw().into_u32()
    }

    fn from_index(u: u32) -> Self {
        let id: TyId = u.into();
        id.into()
    }

    fn tag() -> &'static str {
        "TyIdEqKey"
    }
}

impl UnifyValue for TypeVariableValue {
    type Error = unify::NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (value1, value2) {
            // We never equate two type variables, both of which
            // have known types. Instead, we recursively equate
            // those types.
            (&TypeVariableValue::Known { .. }, &TypeVariableValue::Known { .. }) => {
                unreachable!("equating two type variables, both of which have known types")
            }
            // If one side is known, prefer that one.
            (&TypeVariableValue::Known { .. }, &TypeVariableValue::Unknown) => Ok(value1.clone()),
            (&TypeVariableValue::Unknown, &TypeVariableValue::Known { .. }) => Ok(value1.clone()),

            // both unknown, doesn't matter
            (&TypeVariableValue::Unknown, &TypeVariableValue::Unknown) => {
                Ok(TypeVariableValue::Unknown)
            }
        }
    }
}

impl TypeVariableValue {
    /// If this value is known, returns the type it is known to be.
    /// Otherwise, `None`.
    pub(crate) fn known(&self) -> Option<TyId> {
        match self {
            TypeVariableValue::Unknown => None,
            TypeVariableValue::Known(value) => Some(*value),
        }
    }

    pub(crate) fn is_unknown(&self) -> bool {
        match *self {
            TypeVariableValue::Unknown => true,
            TypeVariableValue::Known { .. } => false,
        }
    }
}

// the poly type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TySchema {
    pub vars: HashSet<usize>, // Each usize corresponds to a Ty::TyVar(x)
    pub ty: TyId,
}

impl Ty<TyId> {
    fn intern_ty(self, ctx: &mut CheckCtx) -> TyId {
        ctx.alloc_ty(Some(self))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraint {
    kind: ConstraintKind,
    location: ExprId,
}

// #[derive(Debug, PartialEq, Eq, Clone)]
// // pub enum TyRef {
// //     Id(TyId),      // unification var
// //     Ref(Ty<TyId>), // a type
// // }
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintKind {
    Eq(TyId, TyId),
}

type Substitutions = HashMap<usize, TyId>;

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    table: InPlaceUnificationTable<TyIdEqKey>,

    arena: Types,

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
            kind: ConstraintKind::Eq(lhs, rhs),
        });
    }

    // pub fn unify_var_ty(&mut self, e: ExprId, lhs: TyId, rhs: Ty<TyId>) {
    //     self.constraints.push(Constraint {
    //         location: e,
    //         kind: ConstraintKind::Eq(lhs, rhs),
    //     });
    // }
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

#[derive(Debug, Clone, PartialEq, Eq, Error)]
enum InferenceError {
    #[error("Could not union {0:?} and {1:?}")]
    InvalidUnion(Ty<TyId>, Ty<TyId>),

    #[error("Unifying attr set {0:?} with empty ")]
    UnifyEmptyRest(AttrSetTy<TyId>),

    #[error("Could union attr set {0:?} and  {1:?}")]
    InvalidAttrUnion(AttrSetTy<TyId>, AttrSetTy<TyId>),
}

impl<'db> CheckCtx<'db> {
    pub fn new(module: &'db Module, name_res: &'db NameResolution) -> Self {
        // let types = TypeTable::new(&module, &name_res);

        // // Init the table with placeholder types for all names and expressions
        // // adding names here allows for recursive references
        // // After we infer a name's value it should be added to the poly_type_env
        // let table = UnionFind::new(module.names().len() + module.exprs().len(), |idx| {
        //     Ty::TyVar(idx.idx())
        // });

        // let types = UnionFind::new(len, make_default);
        Self {
            module,
            name_res,
            arena: Types::new(),
            table: InPlaceUnificationTable::new(),
            poly_type_env: HashMap::new(),
        }
    }

    pub fn infer_prog(&mut self, groups: GroupedDefs) -> InferenceResult {
        for group in groups {
            self.infer_scc_group(group);
        }

        todo!("finalize!!!")
    }

    fn infer_scc_group(&mut self, group: DependentGroup) {
        let mut constraints = ConstraintCtx::new();

        for def in &group {
            self.generate_constraints(&mut constraints, def.expr());
        }

        self.solve_constraints(constraints)
            .expect("TODO: solve error aka type error");

        for def in &group {
            let name_ty = self.ty_for_name(def.name());
            let generalized_val = self.generalize(name_ty);
            self.poly_type_env.insert(def.name(), generalized_val);
        }
    }

    // ---------------------------------
    // GENERATION
    // ---------------------------------

    fn alloc_ty(&mut self, ty: Option<Ty<TyId>>) -> TyId {
        let id = if let Some(t) = ty {
            self.arena.alloc(t)
        } else {
            let next_idx = self.arena.len();
            let t = Ty::TyVar(next_idx);
            self.arena.alloc(t)
        };

        TyId(id)
    }

    fn new_ty_var(&mut self) -> TyId {
        let idx = self.alloc_ty(None);
        let eq_key = self.table.new_key(TypeVariableValue::Unknown);
        debug_assert_eq!(eq_key.id, idx);

        idx
    }

    fn ty_for_name(&mut self, name: NameId) -> TyId {
        let ty_schema = self.poly_type_env.get(&name).cloned();

        if let Some(ty_schema) = ty_schema {
            return self.instantiate(&ty_schema);
        }

        // NOTE: this should only happen during the inference of the value for the name
        // after inferring we should add the name to the poly type env
        u32::from(name.into_raw()).into()
    }

    fn ty_for_expr(&self, i: ExprId) -> TyId {
        let idx = self.module.names().len() as u32 + u32::from(i.into_raw());
        idx.into()
    }

    fn get_ty(&mut self, id: TyId) -> Ty<TyId> {
        let probed = self.table.find(id);

        self.arena[probed.id.0].clone()
    }

    fn instantiate(&mut self, scheme: &TySchema) -> TyId {
        let mut substitutions = HashMap::new();
        for &var in &scheme.vars {
            substitutions.insert(var, self.new_ty_var());
        }

        self.instantiate_ty(scheme.ty, &substitutions)
    }

    fn instantiate_ty(&mut self, ty_id: TyId, substitutions: &Substitutions) -> TyId {
        let Some(ty_id) = self.table.probe_value(ty_id).known() else {
            panic!("TODO instantiate_ty: not sure if it could be unknown by here...")
        };

        let ty = self.arena[ty_id.0].clone();

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
        let mut set = HashSet::new();

        let Some(ty_id) = self.table.probe_value(ty_id).known() else {
            panic!("TODO FTV: not sure if it could be unknown by here in...")
        };

        let ty = self.arena[ty_id.0].clone();

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
                                Ty::Primitive(PrimitiveTy::Int).intern_ty(self),
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

                // TODO: would be nice to have primitives like this cached
                // is that fine to share?
                let str_ty: Ty<TyId> = PrimitiveTy::String.into();
                let str_ty = str_ty.intern_ty(self);

                let ret_ty = attrpath.iter().fold(set_ty, |set_ty, &attr| {
                    let attr_ty = self.generate_constraints(constraints, attr);
                    constraints.unify_var(e, attr_ty, str_ty);
                    let opt_key = match &self.module[attr] {
                        Expr::Literal(Literal::String(key)) => key.clone(),
                        _ => todo!("Dyanmic attr fields not supported yet in select"),
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

    // ---------------------------------
    // Solving
    // ---------------------------------

    fn solve_constraints(&mut self, constraints: ConstraintCtx) -> Result<(), InferenceError> {
        // TODO: this really should loop over multiple times
        // we might not be able to solve all constraints from the start
        // so we need to keep looping until we do a loop without doing anything
        for constraint in constraints.constraints {
            self.solve_constraint(constraint)?;
        }

        Ok(())
    }

    fn solve_constraint(&mut self, constraint: Constraint) -> Result<(), InferenceError> {
        let snapshot = self.table.snapshot();

        let res = match constraint.kind {
            ConstraintKind::Eq(lhs, rhs) => self.unify_var(lhs, rhs),
            // ConstraintKind::Eq(lhs, TyRef::Ref(rhs)) => self.unify_var_ty(lhs, rhs),
        };

        match res {
            Ok(()) => {
                self.table.commit(snapshot);
                Ok(())
            }
            Err(e) => {
                self.table.rollback_to(snapshot);
                Err(e)
            }
        }
    }

    fn unify_var_ty(&mut self, var: TyId, rhs: Ty<TyId>) -> Result<(), InferenceError> {
        // let ret = self.unify(var, rhs.clone())?;
        let rhs = rhs.intern_ty(self);
        self.unify(var, rhs)?;
        self.table.union_value(var, TypeVariableValue::Known(rhs));
        Ok(())
    }

    fn unify_var(&mut self, lhs: TyId, rhs: TyId) -> Result<(), InferenceError> {
        let lhs_val = self.table.inlined_probe_value(lhs);
        let rhs_val = self.table.inlined_probe_value(rhs);

        match (lhs_val, rhs_val) {
            (TypeVariableValue::Known(l), TypeVariableValue::Known(r)) => {
                self.unify(l, r)?;
            }
            _ => {
                self.table.union(lhs, rhs);
            }
        }

        Ok(())
    }

    fn unify(&mut self, lhs: TyId, rhs: TyId) -> Result<(), InferenceError> {
        if lhs == rhs {
            return Ok(());
        }

        match (self.get_ty(lhs), self.get_ty(rhs)) {
            // TODO: Don't think i need a contains in check since how i init the type vars should handle that
            // i things are sad will need to do that and error
            (Ty::TyVar(a), Ty::TyVar(b)) => {
                self.unify_var(TyId::from(a as u32), TyId::from(b as u32))?;
                Ty::TyVar(a)
            }
            (Ty::TyVar(var), other) | (other, Ty::TyVar(var)) => {
                let id = TyId::from(var as u32);
                self.unify_var(id, rhs)?;
                other
            }
            (Ty::List(a), Ty::List(b)) => {
                self.unify_var(a, b)?;
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
                self.unify_var(arg1, arg2)?;
                self.unify_var(ret1, ret2)?;
                Ty::Lambda {
                    param: arg1,
                    body: ret1,
                }
            }
            // TODO: https://bernsteinbear.com/blog/row-poly/
            (Ty::AttrSet(_), Ty::AttrSet(_)) => {
                let lhs = self.flatten_attr(lhs);
                let rhs = self.flatten_attr(rhs);
                return self.unify_attr(lhs, rhs);
            }
            (l, r) if l == r => l,
            (l, r) => return Err(InferenceError::InvalidUnion(l, r)),
        };

        Ok(())
    }

    fn flatten_attr(&mut self, ty_id: TyId) -> AttrSetTy<TyId> {
        let ty = self.get_ty(ty_id);

        match ty {
            Ty::TyVar(v) => {
                let probed = self.get_ty(v.into());
                if let Ty::TyVar(rest) = probed {
                    return AttrSetTy::from_rest(rest.into());
                }
                unreachable!("Rest type {ty:?} did not resolve to a type variable")
            }
            Ty::AttrSet(attr) => {
                let rest = attr.rest.map(|rest| self.flatten_attr(rest));

                if let Some(rest) = rest {
                    attr.merge(rest)
                } else {
                    attr
                }
            }
            _ => unreachable!("Saw {ty:?} when flattening attr, only expecting TyVar or AttrSet"),
        }
    }

    fn unify_attr(
        &mut self,
        lhs: AttrSetTy<TyId>,
        rhs: AttrSetTy<TyId>,
    ) -> Result<(), InferenceError> {
        use itertools::Itertools;
        let lhs_keys: HashSet<&SmolStr> = lhs.keys().collect();
        let rhs_keys: HashSet<&SmolStr> = rhs.keys().collect();

        let shared_keys: HashSet<&SmolStr> = lhs_keys.intersection(&rhs_keys).cloned().collect();

        for k in shared_keys.iter().sorted() {
            let lhs_val = lhs.get(k).unwrap();
            let rhs_val = rhs.get(k).unwrap();
            self.unify(*lhs_val, *rhs_val)?;
        }

        let get_missing = |attr: &AttrSetTy<TyId>, key_set: &HashSet<&SmolStr>| {
            let missing_keys = shared_keys.difference(key_set).cloned().cloned();
            attr.get_sub_set(missing_keys)
        };

        if lhs_keys == rhs_keys {
            // both have the same fields, just need to unify the rest
            return match (lhs.rest, rhs.rest) {
                (Some(lhs_rest), Some(rhs_rest)) => self.unify(lhs_rest, rhs_rest),
                _ => Err(InferenceError::InvalidAttrUnion(lhs, rhs)),
            };
        } else if lhs_keys.is_subset(&rhs_keys) {
            // lhs is missing keys the rhs has
            let lhs_missing = get_missing(&lhs, &lhs_keys);

            if let Some(rest) = rhs.rest {
                // let rhs = self.flatten_attr(rest);
                // return self.unify_attr(lhs_missing, rhs);
                return self.unify_var_ty(rest, Ty::AttrSet(lhs_missing));
            }
            return Err(InferenceError::UnifyEmptyRest(lhs_missing));
        } else if rhs_keys.is_subset(&lhs_keys) {
            // rhs is missing keys the lhs has
            let rhs_missing = get_missing(&rhs, &rhs_keys);

            if let Some(rest) = lhs.rest {
                return self.unify_var_ty(rest, Ty::AttrSet(rhs_missing));
            }
            return Err(InferenceError::UnifyEmptyRest(rhs_missing));
        }

        // both are missing stuff so need to unify the two
        match (lhs.rest, rhs.rest) {
            (Some(_), Some(_)) => {
                let lhs_missing = get_missing(&lhs, &lhs_keys);
                let rhs_missing = get_missing(&rhs, &rhs_keys);

                let rest = self.alloc_ty(None);

                self.unify_var_ty(rest, Ty::AttrSet(lhs_missing))?;
                self.unify_var_ty(rest, Ty::AttrSet(rhs_missing))?;
                Ok(())
            }
            _ => Err(InferenceError::InvalidAttrUnion(lhs, rhs)),
        }
    }
}

#[salsa::tracked]
pub fn check_file_debug(db: &dyn crate::Db, file: NixFile) -> InferenceResult {
    let module = crate::module(db, file);

    let name_res = crate::nameres::name_resolution(db, file);

    let grouped_defs = crate::nameres::group_def(db, file);

    let mut check = CheckCtx::new(&module, &name_res);

    check.infer_prog(grouped_defs)
}
