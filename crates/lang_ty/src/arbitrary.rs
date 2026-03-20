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

fn arb_raw_ty(args: RecursiveParams) -> impl Strategy<Value = RawTy> {
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
