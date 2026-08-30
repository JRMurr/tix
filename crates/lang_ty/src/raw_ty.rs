//! `RawTy`: a Box-recursive mirror of `OutputTy` for test generation.
//!
//! Generators can't build arena-indexed `OutputTy` directly because interning
//! needs mutable arena access mid-generation. They build a `RawTy` tree and
//! `intern_raw` it afterwards. Query methods here back generator filters and
//! test assertions.

use std::collections::BTreeMap;

use crate::{AttrSetTy, OutputTy, PrimitiveTy, TyRef, TypeArena};
use smol_str::SmolStr;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    pub depth: u32,
    pub desired_size: u32,
    pub expected_branch_size: u32,
}

// ==============================================================================
// RawTy — Box-recursive type tree for test generation
// ==============================================================================
//
// Generators can't build arena-indexed OutputTy directly because interning
// requires mutable arena access during generation. RawTy mirrors OutputTy's
// structure with Box recursion; the generated tree is post-processed into
// (TypeArena, TyRef) via intern_raw.

#[derive(Debug, Clone)]
pub enum RawTy {
    TyVar(u32),
    Primitive(PrimitiveTy),
    List(Box<RawTy>),
    Lambda { param: Box<RawTy>, body: Box<RawTy> },
    AttrSet(BTreeMap<SmolStr, RawTy>),
    Union(Vec<RawTy>),
    Intersection(Vec<RawTy>),
    Named(SmolStr, Box<RawTy>),
    Neg(Box<RawTy>),
    Bottom,
    Top,
}

// ==============================================================================
// RawTy query methods — used by PBT filters and assertions
// ==============================================================================

impl RawTy {
    /// Generic tree traversal: returns true if any node matches `pred`.
    fn any_node(&self, pred: &impl Fn(&RawTy) -> bool) -> bool {
        if pred(self) {
            return true;
        }
        match self {
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => inner.any_node(pred),
            RawTy::Lambda { param, body } => param.any_node(pred) || body.any_node(pred),
            RawTy::AttrSet(fields) => fields.values().any(|v| v.any_node(pred)),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.any_node(pred))
            }
            _ => false,
        }
    }

    pub fn contains_intersection(&self) -> bool {
        self.any_node(&|ty| matches!(ty, RawTy::Intersection(_)))
    }

    pub fn contains_neg(&self) -> bool {
        self.any_node(&|ty| matches!(ty, RawTy::Neg(_)))
    }

    pub fn contains_top_or_bottom(&self) -> bool {
        self.any_node(&|ty| matches!(ty, RawTy::Top | RawTy::Bottom))
    }

    pub fn contains_bare_tyvar(&self) -> bool {
        match self {
            RawTy::TyVar(_) => true,
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                inner.contains_bare_tyvar()
            }
            // Lambda params are expected to have TyVars — only check the body.
            RawTy::Lambda { body, .. } => body.contains_bare_tyvar(),
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_bare_tyvar()),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.contains_bare_tyvar())
            }
            _ => false,
        }
    }

    pub fn contains_named(&self) -> bool {
        self.any_node(&|ty| matches!(ty, RawTy::Named(_, _)))
    }

    pub fn contains_union_or_intersection(&self) -> bool {
        self.any_node(&|ty| matches!(ty, RawTy::Union(_) | RawTy::Intersection(_)))
    }

    /// True if any lambda param is not a primitive and not a TyVar.
    pub fn has_non_primitive_lambda_param(&self) -> bool {
        match self {
            RawTy::Lambda { param, body } => {
                let bad_param = !matches!(param.as_ref(), RawTy::Primitive(_) | RawTy::TyVar(_));
                bad_param || body.has_non_primitive_lambda_param()
            }
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                inner.has_non_primitive_lambda_param()
            }
            RawTy::AttrSet(fields) => fields.values().any(|v| v.has_non_primitive_lambda_param()),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.has_non_primitive_lambda_param())
            }
            _ => false,
        }
    }

    /// True if any two lambda params (at different nesting levels) share a type variable.
    pub fn has_shared_tyvar_across_lambda_params(&self) -> bool {
        fn collect_tyvars(ty: &RawTy) -> Vec<u32> {
            match ty {
                RawTy::TyVar(v) => vec![*v],
                RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                    collect_tyvars(inner)
                }
                RawTy::Lambda { param, body } => {
                    let mut vars = collect_tyvars(param);
                    vars.extend(collect_tyvars(body));
                    vars
                }
                RawTy::AttrSet(fields) => fields.values().flat_map(collect_tyvars).collect(),
                RawTy::Union(m) | RawTy::Intersection(m) => {
                    m.iter().flat_map(collect_tyvars).collect()
                }
                _ => vec![],
            }
        }

        fn check(ty: &RawTy, seen_param_vars: &mut std::collections::HashSet<u32>) -> bool {
            match ty {
                RawTy::Lambda { param, body } => {
                    let param_vars = collect_tyvars(param);
                    for v in &param_vars {
                        if !seen_param_vars.insert(*v) {
                            return true;
                        }
                    }
                    check(body, seen_param_vars)
                }
                RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                    check(inner, seen_param_vars)
                }
                RawTy::AttrSet(fields) => fields.values().any(|v| check(v, seen_param_vars)),
                RawTy::Union(m) | RawTy::Intersection(m) => {
                    m.iter().any(|member| check(member, seen_param_vars))
                }
                _ => false,
            }
        }

        check(self, &mut std::collections::HashSet::new())
    }

    /// Collect free type variable ids in DFS order of first appearance, deduplicated.
    /// Matches `TypeArena::free_type_vars` which preserves first-appearance order.
    pub fn free_type_vars(&self) -> Vec<u32> {
        fn collect(ty: &RawTy, vars: &mut Vec<u32>, seen: &mut std::collections::HashSet<u32>) {
            match ty {
                RawTy::TyVar(v) => {
                    if seen.insert(*v) {
                        vars.push(*v);
                    }
                }
                RawTy::Primitive(_) | RawTy::Bottom | RawTy::Top => {}
                RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                    collect(inner, vars, seen)
                }
                RawTy::Lambda { param, body } => {
                    collect(param, vars, seen);
                    collect(body, vars, seen);
                }
                RawTy::AttrSet(fields) => {
                    for v in fields.values() {
                        collect(v, vars, seen);
                    }
                }
                RawTy::Union(m) | RawTy::Intersection(m) => {
                    for member in m {
                        collect(member, vars, seen);
                    }
                }
            }
        }
        let mut vars = Vec::new();
        collect(self, &mut vars, &mut std::collections::HashSet::new());
        vars
    }

    /// Renumber type variables to 0..n-1 in order of first appearance.
    /// Matches `TypeArena::normalize_vars` which uses 0-based numbering.
    pub fn normalize_vars(&self) -> RawTy {
        let vars = self.free_type_vars();
        if vars.is_empty() {
            return self.clone();
        }
        let subs: std::collections::HashMap<u32, u32> = vars
            .into_iter()
            .enumerate()
            .map(|(i, v)| (v, i as u32))
            .collect();
        self.apply_subs(&subs)
    }

    /// Offset all free type variables by `num_free_vars`, updating the counter.
    pub fn offset_free_vars(&self, num_free_vars: &mut usize) -> RawTy {
        let vars = self.free_type_vars();
        if vars.is_empty() {
            return self.clone();
        }
        let subs: std::collections::HashMap<u32, u32> = vars
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, (*num_free_vars + i + 1) as u32))
            .collect();
        *num_free_vars += vars.len();
        self.apply_subs(&subs)
    }

    fn apply_subs(&self, subs: &std::collections::HashMap<u32, u32>) -> RawTy {
        match self {
            RawTy::TyVar(v) => RawTy::TyVar(*subs.get(v).unwrap_or(v)),
            RawTy::Primitive(p) => RawTy::Primitive(*p),
            RawTy::List(inner) => RawTy::List(Box::new(inner.apply_subs(subs))),
            RawTy::Lambda { param, body } => RawTy::Lambda {
                param: Box::new(param.apply_subs(subs)),
                body: Box::new(body.apply_subs(subs)),
            },
            RawTy::AttrSet(fields) => RawTy::AttrSet(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), v.apply_subs(subs)))
                    .collect(),
            ),
            RawTy::Union(m) => RawTy::Union(m.iter().map(|t| t.apply_subs(subs)).collect()),
            RawTy::Intersection(m) => {
                RawTy::Intersection(m.iter().map(|t| t.apply_subs(subs)).collect())
            }
            RawTy::Named(name, inner) => {
                RawTy::Named(name.clone(), Box::new(inner.apply_subs(subs)))
            }
            RawTy::Neg(inner) => RawTy::Neg(Box::new(inner.apply_subs(subs))),
            RawTy::Bottom => RawTy::Bottom,
            RawTy::Top => RawTy::Top,
        }
    }
}

/// Spread free type variables across attrset fields (for PBT code generation).
/// Each field gets unique type variable numbering.
pub fn raw_spread_free_vars(
    fields: &BTreeMap<SmolStr, RawTy>,
    num: &mut usize,
) -> BTreeMap<SmolStr, RawTy> {
    fields
        .iter()
        .map(|(k, v)| {
            let new_v = v.offset_free_vars(num);
            (k.clone(), new_v)
        })
        .collect()
}

/// Intern a RawTy tree into a TypeArena, returning the root TyRef.
pub fn intern_raw(arena: &mut TypeArena, raw: &RawTy) -> TyRef {
    match raw {
        RawTy::TyVar(v) => arena.intern(OutputTy::TyVar(*v)),
        RawTy::Primitive(p) => arena.intern(OutputTy::Primitive(*p)),
        RawTy::List(inner) => {
            let inner = intern_raw(arena, inner);
            arena.intern(OutputTy::List(inner))
        }
        RawTy::Lambda { param, body } => {
            let param = intern_raw(arena, param);
            let body = intern_raw(arena, body);
            arena.intern(OutputTy::Lambda { param, body })
        }
        RawTy::AttrSet(fields) => {
            let fields = fields
                .iter()
                .map(|(k, v)| (k.clone(), intern_raw(arena, v)))
                .collect();
            arena.intern(OutputTy::AttrSet(AttrSetTy::from_fields(fields)))
        }
        RawTy::Union(members) => {
            let members = members.iter().map(|m| intern_raw(arena, m)).collect();
            arena.intern(OutputTy::Union(members))
        }
        RawTy::Intersection(members) => {
            let members = members.iter().map(|m| intern_raw(arena, m)).collect();
            arena.intern(OutputTy::Intersection(members))
        }
        RawTy::Named(name, inner) => {
            let inner = intern_raw(arena, inner);
            arena.intern(OutputTy::Named(name.clone(), inner))
        }
        RawTy::Neg(inner) => {
            let inner = intern_raw(arena, inner);
            arena.intern(OutputTy::Neg(inner))
        }
        RawTy::Bottom => arena.intern(OutputTy::Bottom),
        RawTy::Top => arena.intern(OutputTy::Top),
    }
}

impl Default for RecursiveParams {
    fn default() -> Self {
        Self {
            depth: 4,
            desired_size: 64,
            expected_branch_size: 3,
        }
    }
}
