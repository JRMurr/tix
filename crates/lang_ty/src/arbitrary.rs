use std::collections::BTreeMap;

use crate::{AttrSetTy, OutputTy, PrimitiveTy, Substitutions, TyRef, TypeArena};
use proptest::{
    prelude::{any, prop, prop_oneof, Arbitrary, BoxedStrategy, Just, Strategy},
    prop_compose,
};
use smol_str::SmolStr;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    pub depth: u32,
    pub desired_size: u32,
    pub expected_branch_size: u32,
}

// ==============================================================================
// RawTy — Box-recursive type tree for proptest generation
// ==============================================================================
//
// proptest can't generate arena-indexed OutputTy directly because interning
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
    pub fn contains_intersection(&self) -> bool {
        match self {
            RawTy::Intersection(_) => true,
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                inner.contains_intersection()
            }
            RawTy::Lambda { param, body } => {
                param.contains_intersection() || body.contains_intersection()
            }
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_intersection()),
            RawTy::Union(members) => members.iter().any(|m| m.contains_intersection()),
            _ => false,
        }
    }

    pub fn contains_neg(&self) -> bool {
        match self {
            RawTy::Neg(_) => true,
            RawTy::List(inner) | RawTy::Named(_, inner) => inner.contains_neg(),
            RawTy::Lambda { param, body } => param.contains_neg() || body.contains_neg(),
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_neg()),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.contains_neg())
            }
            _ => false,
        }
    }

    pub fn contains_top_or_bottom(&self) -> bool {
        match self {
            RawTy::Top | RawTy::Bottom => true,
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                inner.contains_top_or_bottom()
            }
            RawTy::Lambda { param, body } => {
                param.contains_top_or_bottom() || body.contains_top_or_bottom()
            }
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_top_or_bottom()),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.contains_top_or_bottom())
            }
            _ => false,
        }
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
        match self {
            RawTy::Named(_, _) => true,
            RawTy::List(inner) | RawTy::Neg(inner) => inner.contains_named(),
            RawTy::Lambda { param, body } => param.contains_named() || body.contains_named(),
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_named()),
            RawTy::Union(members) | RawTy::Intersection(members) => {
                members.iter().any(|m| m.contains_named())
            }
            _ => false,
        }
    }

    pub fn contains_union_or_intersection(&self) -> bool {
        match self {
            RawTy::Union(_) | RawTy::Intersection(_) => true,
            RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
                inner.contains_union_or_intersection()
            }
            RawTy::Lambda { param, body } => {
                param.contains_union_or_intersection() || body.contains_union_or_intersection()
            }
            RawTy::AttrSet(fields) => fields.values().any(|v| v.contains_union_or_intersection()),
            _ => false,
        }
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

/// A generated type with its owning arena. Used by PBT.
#[derive(Debug, Clone)]
pub struct ArbitraryType {
    pub arena: TypeArena,
    pub root: TyRef,
}

impl ArbitraryType {
    pub fn get(&self) -> &OutputTy {
        self.arena.get(self.root)
    }
}

pub fn arb_raw_ty(args: RecursiveParams) -> impl Strategy<Value = RawTy> {
    let leaf = prop_oneof![
        8 => any::<PrimitiveTy>().prop_map(RawTy::Primitive),
        1 => (1..=8u32).prop_map(RawTy::TyVar),
        1 => Just(RawTy::Top),
        1 => Just(RawTy::Bottom),
    ];

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            let inner_boxed = inner.clone().prop_map(Box::new);

            prop_oneof![
                3 => inner_boxed.clone().prop_map(RawTy::List),
                3 => (inner_boxed.clone(), inner_boxed.clone())
                    .prop_map(|(param, body)| RawTy::Lambda { param, body }),
                3 => prop::collection::btree_map(arb_smol_str_ident(), inner.clone(), 0..5)
                    .prop_map(RawTy::AttrSet),
                2 => prop::collection::vec(inner.clone(), 2..5).prop_map(RawTy::Union),
                2 => prop::collection::vec(inner.clone(), 2..5).prop_map(RawTy::Intersection),
                1 => inner_boxed.clone().prop_map(RawTy::Neg),
                1 => (arb_smol_str_ident(), inner_boxed.clone())
                    .prop_map(|(name, t)| RawTy::Named(name, t)),
            ]
        },
    )
}

prop_compose! {
    pub fn arb_smol_str_ident()(string in "_pbt_([a-z]|[A-Z]|[0-9]|_){1,10}") -> SmolStr {
        string.into()
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

impl Arbitrary for ArbitraryType {
    type Parameters = RecursiveParams;
    type Strategy = BoxedStrategy<ArbitraryType>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        arb_raw_ty(args)
            .prop_map(|raw| {
                let mut arena = TypeArena::new();
                let root = intern_raw(&mut arena, &raw);
                ArbitraryType { arena, root }
            })
            .boxed()
    }
}

pub fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
    prop_oneof![
        Just(PrimitiveTy::Null),
        Just(PrimitiveTy::Bool),
        Just(PrimitiveTy::Int),
        Just(PrimitiveTy::Float),
        Just(PrimitiveTy::String),
    ]
    .boxed()
}

impl Arbitrary for PrimitiveTy {
    type Parameters = ();
    type Strategy = BoxedStrategy<PrimitiveTy>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_prim().boxed()
    }
}

// ==============================================================================
// Arena-aware utility methods for PBT
// ==============================================================================

impl TypeArena {
    /// Each child of the attrset gets unique ty vars (for PBT code generation).
    pub fn spread_free_vars(
        &mut self,
        attr: &AttrSetTy<TyRef>,
        num_free_vars: &mut usize,
    ) -> AttrSetTy<TyRef> {
        let fields = attr
            .fields
            .iter()
            .map(|(k, &v)| {
                let free_vars = self.free_type_vars(v);

                let subs: Substitutions = free_vars
                    .iter()
                    .enumerate()
                    .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
                    .collect();

                *num_free_vars += free_vars.len();

                let ty = self.normalize_inner_with_subs(v, &subs);

                (k.clone(), ty)
            })
            .collect();

        AttrSetTy {
            fields,
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        }
    }

    /// Offset all free vars by num_free_vars (for PBT code generation).
    pub fn offset_free_vars(&mut self, ty: TyRef, num_free_vars: &mut usize) -> TyRef {
        let free_vars = self.free_type_vars(ty);

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
            .collect();

        *num_free_vars += free_vars.len();

        self.normalize_inner_with_subs(ty, &subs)
    }

    /// Apply a substitution to normalize vars, using a pre-built substitution map.
    pub fn normalize_inner_with_subs(&mut self, ty: TyRef, subs: &Substitutions) -> TyRef {
        if subs.is_empty() {
            return ty;
        }
        if let OutputTy::TyVar(x) = self[ty] {
            return self.intern(OutputTy::TyVar(*subs.get(&x).unwrap_or(&x)));
        }
        let mut cache = rustc_hash::FxHashMap::default();
        self.normalize_inner_cached(ty, subs, &mut cache)
    }
}
