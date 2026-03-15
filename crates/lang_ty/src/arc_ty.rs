use std::fmt;
use std::sync::{Arc, LazyLock};

use derive_more::Debug;
use rustc_hash::{FxHashMap, FxHashSet};

use smol_str::SmolStr;

use crate::{AttrSetTy, PrimitiveTy};

// ==============================================================================
// OutputTy — the canonical output representation of types
// ==============================================================================
//
// During inference we use `Ty<TyId>` which has 5 variants (no unions/intersections).
// After inference, canonicalization produces `OutputTy` which adds Union and Intersection.
// This separation makes it impossible to accidentally construct a union during inference.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OutputTy {
    #[debug("TyVar({_0:?})")]
    TyVar(u32),

    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),

    #[debug("List({_0:?})")]
    List(TyRef),

    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda { param: TyRef, body: TyRef },

    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<TyRef>),

    /// A union of types (e.g. `int | string`). Produced when different branches
    /// of if-then-else or list elements have different types.
    #[debug("Union({_0:?})")]
    Union(Vec<TyRef>),

    /// An intersection of types (e.g. `(int -> int) & (string -> string)`).
    /// Produced in negative/input positions when a variable has multiple upper bounds.
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<TyRef>),

    /// A type alias name wrapping the fully expanded inner type.
    /// Display shows just the alias name; the inner type is preserved for
    /// structural transparency (e.g. field access on a Named attrset).
    #[debug("Named({_0:?}, {_1:?})")]
    Named(SmolStr, TyRef),

    /// Negation type — `~T`. Used in Boolean-Algebraic Subtyping (BAS) for
    /// precise else-branch narrowing. For example, when `isNull x` is false,
    /// x gets type `a & ~null`. Only produced on atoms (primitives); compound
    /// negation is not needed.
    #[debug("Neg({_0:?})")]
    Neg(TyRef),

    /// The uninhabited (bottom) type, representing contradictions like
    /// `int & ~int`. No values inhabit this type. Displayed as `never`.
    #[debug("Bottom")]
    Bottom,

    /// The universal (top) type, representing tautologies like
    /// `int | ~int`. All values inhabit this type. Displayed as `any`.
    /// Dual to Bottom: identity for intersection (`A & any = A`),
    /// absorbing for union (`A | any = any`).
    #[debug("Top")]
    Top,
}

/// Arc-wrapped OutputTy for recursive type structures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(pub Arc<OutputTy>);

impl PartialOrd for TyRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TyRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

// ==============================================================================
// Primitive interning — pre-allocated TyRefs for common OutputTy values
// ==============================================================================
//
// During canonicalization, many identical OutputTy values (all 8 primitives,
// Top, Bottom) are wrapped in Arc via `TyRef::from()`. With large stubs this
// produces ~40M small Arc allocations. Interning returns a clone of the cached
// Arc (cheap refcount bump) instead of allocating a new one.

struct InternedTyRefs {
    null: TyRef,
    bool_: TyRef,
    int: TyRef,
    float: TyRef,
    string: TyRef,
    path: TyRef,
    uri: TyRef,
    number: TyRef,
    top: TyRef,
    bottom: TyRef,
}

static INTERNED: LazyLock<InternedTyRefs> = LazyLock::new(|| InternedTyRefs {
    null: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Null))),
    bool_: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Bool))),
    int: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Int))),
    float: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Float))),
    string: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::String))),
    path: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Path))),
    uri: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Uri))),
    number: TyRef(Arc::new(OutputTy::Primitive(PrimitiveTy::Number))),
    top: TyRef(Arc::new(OutputTy::Top)),
    bottom: TyRef(Arc::new(OutputTy::Bottom)),
});

impl TyRef {
    /// Return a TyRef for the given OutputTy, using a cached Arc for
    /// primitives, Top, and Bottom. Falls through to `Arc::new` for
    /// compound types.
    pub fn interned(ty: OutputTy) -> Self {
        match &ty {
            OutputTy::Primitive(p) => match p {
                PrimitiveTy::Null => INTERNED.null.clone(),
                PrimitiveTy::Bool => INTERNED.bool_.clone(),
                PrimitiveTy::Int => INTERNED.int.clone(),
                PrimitiveTy::Float => INTERNED.float.clone(),
                PrimitiveTy::String => INTERNED.string.clone(),
                PrimitiveTy::Path => INTERNED.path.clone(),
                PrimitiveTy::Uri => INTERNED.uri.clone(),
                PrimitiveTy::Number => INTERNED.number.clone(),
            },
            OutputTy::Top => INTERNED.top.clone(),
            OutputTy::Bottom => INTERNED.bottom.clone(),
            _ => TyRef(Arc::new(ty)),
        }
    }
}

impl From<OutputTy> for TyRef {
    fn from(value: OutputTy) -> Self {
        TyRef::interned(value)
    }
}

impl PartialOrd for OutputTy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OutputTy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        /// Discriminant index for ordering OutputTy variants.
        fn disc(ty: &OutputTy) -> u8 {
            match ty {
                OutputTy::Bottom => 0,
                OutputTy::Top => 1,
                OutputTy::Primitive(_) => 2,
                OutputTy::TyVar(_) => 3,
                OutputTy::List(_) => 4,
                OutputTy::Lambda { .. } => 5,
                OutputTy::AttrSet(_) => 6,
                OutputTy::Union(_) => 7,
                OutputTy::Intersection(_) => 8,
                OutputTy::Named(..) => 9,
                OutputTy::Neg(_) => 10,
            }
        }

        let d = disc(self).cmp(&disc(other));
        if d != Ordering::Equal {
            return d;
        }

        match (self, other) {
            (OutputTy::Bottom, OutputTy::Bottom) | (OutputTy::Top, OutputTy::Top) => {
                Ordering::Equal
            }
            (OutputTy::Primitive(a), OutputTy::Primitive(b)) => a.cmp(b),
            (OutputTy::TyVar(a), OutputTy::TyVar(b)) => a.cmp(b),
            (OutputTy::List(a), OutputTy::List(b)) => a.cmp(b),
            (
                OutputTy::Lambda {
                    param: pa,
                    body: ba,
                },
                OutputTy::Lambda {
                    param: pb,
                    body: bb,
                },
            ) => pa.cmp(pb).then_with(|| ba.cmp(bb)),
            (OutputTy::AttrSet(a), OutputTy::AttrSet(b)) => a.cmp(b),
            (OutputTy::Union(a), OutputTy::Union(b))
            | (OutputTy::Intersection(a), OutputTy::Intersection(b)) => a.cmp(b),
            (OutputTy::Named(na, ta), OutputTy::Named(nb, tb)) => {
                na.cmp(nb).then_with(|| ta.cmp(tb))
            }
            (OutputTy::Neg(a), OutputTy::Neg(b)) => a.cmp(b),
            // Same discriminant → same variant; already handled above.
            _ => unreachable!(),
        }
    }
}

pub type Substitutions = FxHashMap<u32, u32>;

// ==============================================================================
// Normalization and free variable collection on OutputTy
// ==============================================================================

impl OutputTy {
    /// Returns true if this type or any of its children contains a TyVar.
    /// Short-circuits on first hit — O(1) for concrete types, O(n) worst case.
    /// Uses a visited set to avoid exponential blowup on DAG-shaped types.
    pub fn has_type_vars(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.has_type_vars_inner(&mut visited)
    }

    fn has_type_vars_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        if let OutputTy::TyVar(_) = self {
            return true;
        }
        let mut found = false;
        self.for_each_child_tyref(&mut |child| {
            if !found && visited.insert(Arc::as_ptr(&child.0)) {
                found = child.0.has_type_vars_inner(visited);
            }
        });
        found
    }

    /// Normalize all the ty vars to start from 0 instead
    /// of the "random" nums it has from solving.
    pub fn normalize_vars(&self) -> OutputTy {
        // Concrete types with no TyVar nodes are already normalized — skip the
        // full tree walk + rebuild. This is the common case for NixOS config
        // attrsets with hundreds of fields, avoiding ~7 GB of map_children
        // allocations in large stubs.
        if !self.has_type_vars() {
            return self.clone();
        }

        let free_vars = self.free_type_vars();

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, i as u32))
            .collect();

        // Handle root TyVar directly (no need to wrap in Arc).
        if let OutputTy::TyVar(x) = self {
            return OutputTy::TyVar(*subs.get(x).unwrap());
        }
        let mut cache = FxHashMap::default();
        self.map_children_tyref(&mut |child| Self::normalize_inner_cached(child, &subs, &mut cache))
    }

    /// Memoized normalize_inner that caches by Arc pointer identity.
    /// When the same `Arc<OutputTy>` subtree is encountered via a different
    /// parent, the cached result is returned (Arc refcount bump) instead of
    /// re-traversing and re-allocating. This prevents DAG-to-tree explosion.
    fn normalize_inner_cached(
        tyref: &TyRef,
        free: &Substitutions,
        cache: &mut FxHashMap<*const OutputTy, TyRef>,
    ) -> TyRef {
        let ptr = Arc::as_ptr(&tyref.0);
        if let Some(cached) = cache.get(&ptr) {
            return cached.clone();
        }
        let result =
            stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
                if let OutputTy::TyVar(x) = &*tyref.0 {
                    return TyRef::from(OutputTy::TyVar(*free.get(x).unwrap()));
                }
                TyRef::from(tyref.0.map_children_tyref(&mut |child| {
                    Self::normalize_inner_cached(child, free, cache)
                }))
            });
        cache.insert(ptr, result.clone());
        result
    }

    /// Public normalize_inner for callers (e.g. PBT arbitrary) that already
    /// have a substitution map. Delegates to the cached version.
    pub fn normalize_inner(&self, free: &Substitutions) -> OutputTy {
        if let OutputTy::TyVar(x) = self {
            return OutputTy::TyVar(*free.get(x).unwrap());
        }
        let mut cache = FxHashMap::default();
        self.map_children_tyref(&mut |child| Self::normalize_inner_cached(child, free, &mut cache))
    }

    /// Returns true if any Lambda in this type has a non-primitive param type.
    /// Such types can't be precisely generated in PBT because the `if param == <value>`
    /// code generation pattern doesn't fully constrain non-primitive params in
    /// SimpleSub's polarity-aware canonicalization.
    pub fn has_non_primitive_lambda_param(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.has_non_primitive_lambda_param_inner(&mut visited)
    }

    fn has_non_primitive_lambda_param_inner(
        &self,
        visited: &mut FxHashSet<*const OutputTy>,
    ) -> bool {
        if let OutputTy::Lambda { param, .. } = self {
            if !matches!(&*param.0, OutputTy::Primitive(_) | OutputTy::TyVar(_)) {
                return true;
            }
        }
        let mut found = false;
        self.for_each_child_tyref(&mut |child| {
            if !found && visited.insert(Arc::as_ptr(&child.0)) {
                found = child.0.has_non_primitive_lambda_param_inner(visited);
            }
        });
        found
    }

    /// Returns true if this type or any of its children contains a Union or Intersection.
    pub fn contains_union_or_intersection(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_union_or_intersection_inner(&mut visited)
    }

    fn contains_union_or_intersection_inner(
        &self,
        visited: &mut FxHashSet<*const OutputTy>,
    ) -> bool {
        match self {
            OutputTy::Union(_) | OutputTy::Intersection(_) => true,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_union_or_intersection_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Returns true if this type or any of its children contains an Intersection.
    pub fn contains_intersection(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_intersection_inner(&mut visited)
    }

    fn contains_intersection_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        match self {
            OutputTy::Intersection(_) => true,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_intersection_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Returns true if this type or any of its children contains a Neg.
    pub fn contains_neg(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_neg_inner(&mut visited)
    }

    fn contains_neg_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        match self {
            OutputTy::Neg(_) => true,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_neg_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Returns true if this type is or contains Top or Bottom.
    pub fn contains_top_or_bottom(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_top_or_bottom_inner(&mut visited)
    }

    fn contains_top_or_bottom_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        match self {
            OutputTy::Top | OutputTy::Bottom => true,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_top_or_bottom_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Returns true if this type is or contains a bare TyVar outside of Lambda params.
    /// TyVar is fine inside Lambda params (represents generic params), but can't be
    /// generated as standalone Nix code.
    pub fn contains_bare_tyvar(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_bare_tyvar_inner(&mut visited)
    }

    fn contains_bare_tyvar_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        match self {
            OutputTy::TyVar(_) => true,
            // Lambda params are allowed to have TyVar, so only check body
            OutputTy::Lambda { body, .. } => {
                if visited.insert(Arc::as_ptr(&body.0)) {
                    body.0.contains_bare_tyvar_inner(visited)
                } else {
                    false
                }
            }
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_bare_tyvar_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Recursively flatten, deduplicate, and sort Union/Intersection members
    /// for order-insensitive comparison. The type checker flattens nested
    /// unions and may reorder/deduplicate members during canonicalization.
    pub fn normalize_set_ops(&self) -> OutputTy {
        let mut cache = FxHashMap::default();
        self.normalize_set_ops_cached(&mut cache)
    }

    fn normalize_set_ops_cached(&self, cache: &mut FxHashMap<*const OutputTy, TyRef>) -> OutputTy {
        match self {
            OutputTy::Union(members) => {
                let mut flat: Vec<TyRef> = Vec::new();
                Self::flatten_union_cached(members, &mut flat, cache);
                flat.sort();
                flat.dedup();
                if flat.len() == 1 {
                    return flat.into_iter().next().unwrap().0.as_ref().clone();
                }
                OutputTy::Union(flat)
            }
            OutputTy::Intersection(members) => {
                let mut flat: Vec<TyRef> = Vec::new();
                Self::flatten_intersection_cached(members, &mut flat, cache);
                flat.sort();
                flat.dedup();
                if flat.len() == 1 {
                    return flat.into_iter().next().unwrap().0.as_ref().clone();
                }
                OutputTy::Intersection(flat)
            }
            _ => self.map_children_tyref(&mut |child| {
                Self::normalize_set_ops_tyref_cached(child, cache)
            }),
        }
    }

    fn normalize_set_ops_tyref_cached(
        tyref: &TyRef,
        cache: &mut FxHashMap<*const OutputTy, TyRef>,
    ) -> TyRef {
        let ptr = Arc::as_ptr(&tyref.0);
        if let Some(cached) = cache.get(&ptr) {
            return cached.clone();
        }
        let result = TyRef::from(tyref.0.normalize_set_ops_cached(cache));
        cache.insert(ptr, result.clone());
        result
    }

    fn flatten_union_cached(
        members: &[TyRef],
        out: &mut Vec<TyRef>,
        cache: &mut FxHashMap<*const OutputTy, TyRef>,
    ) {
        for m in members {
            let normalized = m.0.normalize_set_ops_cached(cache);
            if let OutputTy::Union(inner) = &normalized {
                out.extend(inner.iter().cloned());
            } else {
                out.push(TyRef::from(normalized));
            }
        }
    }

    fn flatten_intersection_cached(
        members: &[TyRef],
        out: &mut Vec<TyRef>,
        cache: &mut FxHashMap<*const OutputTy, TyRef>,
    ) {
        for m in members {
            let normalized = m.0.normalize_set_ops_cached(cache);
            if let OutputTy::Intersection(inner) = &normalized {
                out.extend(inner.iter().cloned());
            } else {
                out.push(TyRef::from(normalized));
            }
        }
    }

    /// Returns true if any TyVar index appears in Lambda param position more
    /// than once across distinct Lambdas. This happens when the PBT generator
    /// produces types like `TyVar(1) -> TyVar(1) -> int` — the code generator
    /// creates independent shadowing params, so the checker infers distinct
    /// variables where the type expects shared ones.
    pub fn has_shared_tyvar_across_lambda_params(&self) -> bool {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut visited = FxHashSet::default();
        self.check_shared_lambda_param_tyvars(&mut seen, &mut visited)
    }

    /// Walk the type tree collecting TyVar indices from Lambda param positions.
    /// Returns true as soon as a duplicate is found.
    fn check_shared_lambda_param_tyvars(
        &self,
        seen: &mut rustc_hash::FxHashSet<u32>,
        visited: &mut FxHashSet<*const OutputTy>,
    ) -> bool {
        match self {
            OutputTy::Lambda { param, body } => {
                if let OutputTy::TyVar(idx) = &*param.0 {
                    if !seen.insert(*idx) {
                        return true;
                    }
                }
                // Recurse into param (for nested lambdas in param position)
                // and body (for chained lambdas like `a -> b -> c`).
                (visited.insert(Arc::as_ptr(&param.0))
                    && param.0.check_shared_lambda_param_tyvars(seen, visited))
                    || (visited.insert(Arc::as_ptr(&body.0))
                        && body.0.check_shared_lambda_param_tyvars(seen, visited))
            }
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => false,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.check_shared_lambda_param_tyvars(seen, visited);
                    }
                });
                found
            }
        }
    }

    /// Returns true if this type contains a Named wrapper.
    pub fn contains_named(&self) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_named_inner(&mut visited)
    }

    fn contains_named_inner(&self, visited: &mut FxHashSet<*const OutputTy>) -> bool {
        match self {
            OutputTy::Named(..) => true,
            _ => {
                let mut found = false;
                self.for_each_child_tyref(&mut |child| {
                    if !found && visited.insert(Arc::as_ptr(&child.0)) {
                        found = child.0.contains_named_inner(visited);
                    }
                });
                found
            }
        }
    }

    /// Like `normalize_vars`, but displays `?` when the entire type is a bare
    /// type variable (meaning "unconstrained / unknown"). Compound types like
    /// `a -> b -> a` keep normal letter names — those variables represent real
    /// parameter types, not unknowns.
    pub fn normalize_replacing_unknown(&self) -> OutputTy {
        if matches!(self, OutputTy::TyVar(_)) {
            return OutputTy::TyVar(UNKNOWN_TYVAR);
        }
        self.normalize_vars()
    }

    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        let mut visited = FxHashSet::default();
        self.collect_free_type_vars(&mut result, &mut seen, &mut visited);
        result
    }

    fn collect_free_type_vars(
        &self,
        result: &mut Vec<u32>,
        seen: &mut rustc_hash::FxHashSet<u32>,
        visited: &mut FxHashSet<*const OutputTy>,
    ) {
        if let OutputTy::TyVar(x) = self {
            if seen.insert(*x) {
                result.push(*x);
            }
            return;
        }
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            self.for_each_child_tyref(&mut |child| {
                if visited.insert(Arc::as_ptr(&child.0)) {
                    child.0.collect_free_type_vars(result, seen, visited);
                }
            });
        });
    }

    // ==========================================================================
    // Child traversal helpers
    // ==========================================================================
    //
    // Centralise the "recurse into direct children" logic so that new OutputTy
    // variants only need one update site. These are intentionally shallow — they
    // apply `f` to each direct child but do NOT recurse; callers compose
    // recursion themselves.

    /// Apply `f` to every direct child, producing a new OutputTy with the same
    /// variant structure. Leaf variants (TyVar, Primitive) are returned as-is.
    pub fn map_children(&self, f: &mut impl FnMut(&OutputTy) -> OutputTy) -> OutputTy {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {
                self.clone()
            }
            OutputTy::List(inner) => OutputTy::List(f(&inner.0).into()),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: f(&param.0).into(),
                body: f(&body.0).into(),
            },
            OutputTy::AttrSet(attr) => {
                let fields = attr
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), f(&v.0).into()))
                    .collect();
                let dyn_ty = attr.dyn_ty.as_ref().map(|d| f(&d.0).into());
                OutputTy::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            OutputTy::Union(members) => {
                OutputTy::Union(members.iter().map(|m| f(&m.0).into()).collect())
            }
            OutputTy::Intersection(members) => {
                OutputTy::Intersection(members.iter().map(|m| f(&m.0).into()).collect())
            }
            OutputTy::Named(name, inner) => OutputTy::Named(name.clone(), f(&inner.0).into()),
            OutputTy::Neg(inner) => OutputTy::Neg(f(&inner.0).into()),
        }
    }

    /// Visit every direct child for read-only inspection. Leaf variants
    /// (TyVar, Primitive) have no children, so `f` is never called on them.
    pub fn for_each_child(&self, f: &mut impl FnMut(&OutputTy)) {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {}
            OutputTy::List(inner) => f(&inner.0),
            OutputTy::Lambda { param, body } => {
                f(&param.0);
                f(&body.0);
            }
            OutputTy::AttrSet(attr) => {
                for v in attr.fields.values() {
                    f(&v.0);
                }
                if let Some(dyn_ty) = &attr.dyn_ty {
                    f(&dyn_ty.0);
                }
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for m in members {
                    f(&m.0);
                }
            }
            OutputTy::Named(_, inner) => f(&inner.0),
            OutputTy::Neg(inner) => f(&inner.0),
        }
    }

    // ==========================================================================
    // TyRef-preserving child traversal helpers
    // ==========================================================================
    //
    // Like map_children/for_each_child but pass `&TyRef` instead of `&OutputTy`.
    // This preserves Arc identity so callers can use Arc::as_ptr for cache keys,
    // which is essential for memoizing DAG walks without exponential blowup.

    /// Apply `f` to every direct child TyRef, producing a new OutputTy with the
    /// same variant structure. `f` receives and returns `TyRef`, preserving Arc
    /// identity for cache-based memoization.
    fn map_children_tyref(&self, f: &mut impl FnMut(&TyRef) -> TyRef) -> OutputTy {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {
                self.clone()
            }
            OutputTy::List(inner) => OutputTy::List(f(inner)),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: f(param),
                body: f(body),
            },
            OutputTy::AttrSet(attr) => {
                let fields = attr.fields.iter().map(|(k, v)| (k.clone(), f(v))).collect();
                let dyn_ty = attr.dyn_ty.as_ref().map(f);
                OutputTy::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            OutputTy::Union(members) => OutputTy::Union(members.iter().map(f).collect()),
            OutputTy::Intersection(members) => {
                OutputTy::Intersection(members.iter().map(f).collect())
            }
            OutputTy::Named(name, inner) => OutputTy::Named(name.clone(), f(inner)),
            OutputTy::Neg(inner) => OutputTy::Neg(f(inner)),
        }
    }

    /// Visit every direct child TyRef for read-only inspection. Like
    /// `for_each_child` but preserves Arc identity.
    fn for_each_child_tyref(&self, f: &mut impl FnMut(&TyRef)) {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {}
            OutputTy::List(inner) => f(inner),
            OutputTy::Lambda { param, body } => {
                f(param);
                f(body);
            }
            OutputTy::AttrSet(attr) => {
                for v in attr.fields.values() {
                    f(v);
                }
                if let Some(dyn_ty) = &attr.dyn_ty {
                    f(dyn_ty);
                }
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for m in members {
                    f(m);
                }
            }
            OutputTy::Named(_, inner) => f(inner),
            OutputTy::Neg(inner) => f(inner),
        }
    }
}

// ==============================================================================
// Display — human-readable type printing
// ==============================================================================
//
// Type variables are rendered as lowercase letters (a, b, c, ..., z, a1, b1, ...).
// Operator precedence is handled by checking whether parentheses are needed:
//   `->` is right-associative and lowest precedence
//   `|` is next
//   `&` is next
//   atoms (primitives, lists, attrsets, type vars) are highest

/// Sentinel index for type variables that should display as `?` (unknown type).
const UNKNOWN_TYVAR: u32 = u32::MAX;

/// Convert a type variable index to a letter-based name: 0→a, 1→b, ..., 25→z, 26→a1, ...
/// The sentinel value `UNKNOWN_TYVAR` renders as `?`.
fn tyvar_name(idx: u32) -> String {
    if idx == UNKNOWN_TYVAR {
        return "?".to_string();
    }
    let letter = (b'a' + (idx % 26) as u8) as char;
    let suffix = idx / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{letter}{suffix}")
    }
}

impl fmt::Display for OutputTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Guard against stack overflow on deeply nested type trees.
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || match self {
            OutputTy::TyVar(x) => write!(f, "{}", tyvar_name(*x)),
            OutputTy::Primitive(p) => write!(f, "{p}"),
            OutputTy::List(inner) => write!(f, "[{inner}]"),
            OutputTy::Lambda { param, body } => {
                // Parenthesize the param if it's a lambda, union, or intersection
                // to avoid ambiguity (-> is right-associative).
                let needs_parens = matches!(
                    &*param.0,
                    OutputTy::Lambda { .. } | OutputTy::Union(_) | OutputTy::Intersection(_)
                );
                if needs_parens {
                    write!(f, "({param}) -> {body}")
                } else {
                    write!(f, "{param} -> {body}")
                }
            }
            OutputTy::AttrSet(attr) => write!(f, "{attr}"),
            OutputTy::Union(members) => {
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    // Parenthesize lambdas inside unions to avoid ambiguity.
                    let needs_parens = matches!(&*m.0, OutputTy::Lambda { .. });
                    if needs_parens {
                        write!(f, "({m})")?;
                    } else {
                        write!(f, "{m}")?;
                    }
                }
                Ok(())
            }
            OutputTy::Intersection(members) => {
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " & ")?;
                    }
                    // Parenthesize lambdas and unions inside intersections.
                    let needs_parens =
                        matches!(&*m.0, OutputTy::Lambda { .. } | OutputTy::Union(_));
                    if needs_parens {
                        write!(f, "({m})")?;
                    } else {
                        write!(f, "{m}")?;
                    }
                }
                Ok(())
            }
            OutputTy::Named(name, _) => write!(f, "{name}"),
            OutputTy::Neg(inner) => {
                // Parenthesize compound types inside negation for clarity.
                let needs_parens = matches!(
                    &*inner.0,
                    OutputTy::Union(_) | OutputTy::Intersection(_) | OutputTy::Lambda { .. }
                );
                if needs_parens {
                    write!(f, "~({inner})")
                } else {
                    write!(f, "~{inner}")
                }
            }
            OutputTy::Bottom => write!(f, "never"),
            OutputTy::Top => write!(f, "any"),
        })
    }
}

impl fmt::Display for TyRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&*self.0, f)
    }
}

impl fmt::Display for PrimitiveTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimitiveTy::Null => write!(f, "null"),
            PrimitiveTy::Bool => write!(f, "bool"),
            PrimitiveTy::Int => write!(f, "int"),
            PrimitiveTy::Float => write!(f, "float"),
            PrimitiveTy::String => write!(f, "string"),
            PrimitiveTy::Path => write!(f, "path"),
            PrimitiveTy::Uri => write!(f, "uri"),
            PrimitiveTy::Number => write!(f, "number"),
        }
    }
}

impl fmt::Display for AttrSetTy<TyRef> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        let mut first = true;
        for (k, v) in self.fields.iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            let opt = if self.optional_fields.contains(k) {
                "?"
            } else {
                ""
            };
            write!(f, "{k}{opt}: {v}")?;
        }
        if let Some(dyn_ty) = &self.dyn_ty {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "_: {dyn_ty}")?;
        }
        if self.open {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        write!(f, " }}")
    }
}

impl AttrSetTy<TyRef> {
    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        for v in self.fields.values() {
            for var in v.0.free_type_vars() {
                if seen.insert(var) {
                    result.push(var);
                }
            }
        }
        if let Some(dyn_ty) = &self.dyn_ty {
            for var in dyn_ty.0.free_type_vars() {
                if seen.insert(var) {
                    result.push(var);
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize_replacing_unknown_bare_tyvar() {
        // A standalone TyVar appears once → replaced with `?`.
        let ty = OutputTy::TyVar(5);
        let result = ty.normalize_replacing_unknown();
        assert_eq!(format!("{result}"), "?");
    }

    #[test]
    fn normalize_replacing_unknown_compound_keeps_letters() {
        // Compound types use normal normalize_vars — all vars get letters.
        let ty = OutputTy::Lambda {
            param: OutputTy::TyVar(0).into(),
            body: OutputTy::TyVar(0).into(),
        };
        let result = ty.normalize_replacing_unknown();
        assert_eq!(format!("{result}"), "a -> a");

        // const :: a -> b -> a — b is a real parameter, not unknown.
        let ty = OutputTy::Lambda {
            param: OutputTy::TyVar(0).into(),
            body: OutputTy::Lambda {
                param: OutputTy::TyVar(1).into(),
                body: OutputTy::TyVar(0).into(),
            }
            .into(),
        };
        let result = ty.normalize_replacing_unknown();
        assert_eq!(format!("{result}"), "a -> b -> a");
    }

    #[test]
    fn normalize_replacing_unknown_no_tyvars() {
        // int -> string: no TyVars → unchanged.
        let ty = OutputTy::Lambda {
            param: OutputTy::Primitive(PrimitiveTy::Int).into(),
            body: OutputTy::Primitive(PrimitiveTy::String).into(),
        };
        let result = ty.normalize_replacing_unknown();
        assert_eq!(format!("{result}"), "int -> string");
    }

    #[test]
    fn number_displays_as_number() {
        // Number in lambda position must not produce "int | float -> int | float"
        // (which looks like a 3-member union). It should display as "number -> number".
        let ty = OutputTy::Lambda {
            param: OutputTy::Primitive(PrimitiveTy::Number).into(),
            body: OutputTy::Primitive(PrimitiveTy::Number).into(),
        };
        assert_eq!(format!("{ty}"), "number -> number");
    }

    #[test]
    fn number_displays_standalone() {
        let ty = OutputTy::Primitive(PrimitiveTy::Number);
        assert_eq!(format!("{ty}"), "number");
    }

    #[test]
    fn interned_primitives_share_arc() {
        // TyRef::interned should return the same Arc pointer for identical
        // primitive types, Top, and Bottom — verifying the interning cache.
        let a = TyRef::interned(OutputTy::Primitive(PrimitiveTy::Int));
        let b = TyRef::interned(OutputTy::Primitive(PrimitiveTy::Int));
        assert!(Arc::ptr_eq(&a.0, &b.0), "interned Int should share Arc");

        let c = TyRef::interned(OutputTy::Top);
        let d = TyRef::interned(OutputTy::Top);
        assert!(Arc::ptr_eq(&c.0, &d.0), "interned Top should share Arc");

        let e = TyRef::interned(OutputTy::Bottom);
        let f = TyRef::interned(OutputTy::Bottom);
        assert!(Arc::ptr_eq(&e.0, &f.0), "interned Bottom should share Arc");

        // TyRef::from also goes through interning.
        let g: TyRef = OutputTy::Primitive(PrimitiveTy::String).into();
        let h: TyRef = OutputTy::Primitive(PrimitiveTy::String).into();
        assert!(Arc::ptr_eq(&g.0, &h.0), "From<OutputTy> should intern");
    }

    #[test]
    fn shared_tyvar_across_lambda_params_detected() {
        // TyVar(1) -> TyVar(1) -> int: same var in two Lambda params → true
        let ty = OutputTy::Lambda {
            param: OutputTy::TyVar(1).into(),
            body: OutputTy::Lambda {
                param: OutputTy::TyVar(1).into(),
                body: OutputTy::Primitive(PrimitiveTy::Int).into(),
            }
            .into(),
        };
        assert!(ty.has_shared_tyvar_across_lambda_params());
    }

    #[test]
    fn distinct_tyvar_across_lambda_params_ok() {
        // TyVar(1) -> TyVar(2) -> int: distinct vars → false
        let ty = OutputTy::Lambda {
            param: OutputTy::TyVar(1).into(),
            body: OutputTy::Lambda {
                param: OutputTy::TyVar(2).into(),
                body: OutputTy::Primitive(PrimitiveTy::Int).into(),
            }
            .into(),
        };
        assert!(!ty.has_shared_tyvar_across_lambda_params());
    }

    #[test]
    fn tyvar_in_param_and_body_not_shared() {
        // TyVar(1) -> TyVar(1): same var in param + body of one Lambda → false
        let ty = OutputTy::Lambda {
            param: OutputTy::TyVar(1).into(),
            body: OutputTy::TyVar(1).into(),
        };
        assert!(!ty.has_shared_tyvar_across_lambda_params());
    }

    #[test]
    fn no_lambda_no_sharing() {
        assert!(!OutputTy::Primitive(PrimitiveTy::Int).has_shared_tyvar_across_lambda_params());
    }

    #[test]
    fn shared_tyvar_nested_in_list() {
        // [TyVar(1) -> TyVar(1) -> int]: sharing detected inside list element
        let inner = OutputTy::Lambda {
            param: OutputTy::TyVar(1).into(),
            body: OutputTy::Lambda {
                param: OutputTy::TyVar(1).into(),
                body: OutputTy::Primitive(PrimitiveTy::Int).into(),
            }
            .into(),
        };
        let ty = OutputTy::List(inner.into());
        assert!(ty.has_shared_tyvar_across_lambda_params());
    }

    #[test]
    fn normalize_vars_preserves_dag_sharing() {
        // Build a DAG: 30 levels of Lambda { param: shared, body: shared }.
        // 2^30 paths but only 31 unique nodes.
        // Without memoization: OOM. With memoization: instant.
        let leaf = TyRef::from(OutputTy::TyVar(99));
        let mut current = leaf;
        for _ in 0..30 {
            current = TyRef::from(OutputTy::Lambda {
                param: current.clone(),
                body: current.clone(),
            });
        }
        let result = current.0.normalize_vars();
        // Check the innermost leaf was renumbered to 0.
        fn extract_leaf(ty: &OutputTy) -> Option<u32> {
            match ty {
                OutputTy::TyVar(x) => Some(*x),
                OutputTy::Lambda { param, .. } => extract_leaf(&param.0),
                _ => None,
            }
        }
        assert_eq!(extract_leaf(&result), Some(0));
        // Verify sharing is preserved: the result should also be a DAG.
        // The root Lambda's param and body should point to the same Arc.
        if let OutputTy::Lambda { param, body } = &result {
            assert!(
                Arc::ptr_eq(&param.0, &body.0),
                "normalize_vars should preserve DAG sharing"
            );
        } else {
            panic!("expected Lambda at root");
        }
    }

    #[test]
    fn read_only_predicates_handle_deep_dag() {
        let leaf = TyRef::from(OutputTy::TyVar(42));
        let mut current = leaf;
        for _ in 0..30 {
            current = TyRef::from(OutputTy::Lambda {
                param: current.clone(),
                body: current.clone(),
            });
        }
        assert!(current.0.has_type_vars());
        assert_eq!(current.0.free_type_vars(), vec![42]);
        // These should complete without exponential blowup.
        assert!(!current.0.contains_union_or_intersection());
        assert!(!current.0.contains_neg());
        assert!(!current.0.contains_top_or_bottom());
        assert!(current.0.contains_bare_tyvar());
    }

    #[test]
    fn normalize_set_ops_handles_deep_dag() {
        // normalize_set_ops should not explode on a shared DAG.
        // Completing without OOM is the main assertion.
        let leaf = TyRef::from(OutputTy::Primitive(PrimitiveTy::Int));
        let mut current = leaf;
        for _ in 0..30 {
            current = TyRef::from(OutputTy::Lambda {
                param: current.clone(),
                body: current.clone(),
            });
        }
        let result = current.0.normalize_set_ops();
        // Verify sharing is preserved in the output.
        if let OutputTy::Lambda { param, body } = &result {
            assert!(
                Arc::ptr_eq(&param.0, &body.0),
                "normalize_set_ops should preserve DAG sharing"
            );
        } else {
            panic!("expected Lambda at root");
        }
    }

    mod pbt {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig {
                cases: 256, .. ProptestConfig::default()
            })]

            /// normalize_vars is idempotent: normalizing twice produces the same
            /// result as normalizing once.
            #[test]
            fn normalize_vars_idempotent(ty in any::<OutputTy>()) {
                let once = ty.normalize_vars();
                let twice = once.normalize_vars();
                prop_assert_eq!(once, twice);
            }
        }
    }
}
