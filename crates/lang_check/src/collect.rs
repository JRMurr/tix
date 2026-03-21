// ==============================================================================
// Polarity-Aware Canonicalization
// ==============================================================================
//
// Converts internal TyId representation to canonical OutputTy.
// Variables are expanded based on polarity:
// - Positive position (output): variable → union of lower bounds
// - Negative position (input): variable → intersection of upper bounds
// Lambda params flip polarity.

use std::collections::BTreeMap;
use std::time::Instant;

use la_arena::ArenaMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use smol_str::SmolStr;

use super::{CheckCtx, InferenceResult, Polarity, TyId};
use crate::storage::{TypeEntry, TypeStorage};
use lang_ty::{
    arena::import_from_arena,
    disjoint::{are_shapes_disjoint, ConstructorShape},
    AttrSetTy, OutputTy, Ty, TyRef, TypeArena,
};

use Polarity::{Negative, Positive};

// ==============================================================================
// Canonicalizer — shared canonicalization engine
// ==============================================================================
//
// Both the standalone (mid-inference snapshot) and the Collector (post-inference
// final pass) use the same canonicalization logic, parameterized only by the
// TypeStorage reference. This eliminates the previous duplication between
// StandaloneCanon and Collector's canonicalize methods.

/// How often (in calls to canonicalize) to check the deadline. Avoids
/// Instant::now() syscall overhead on every call — 512 is a reasonable
/// tradeoff between responsiveness and overhead.
const CANON_DEADLINE_CHECK_INTERVAL: u32 = 512;

struct Canonicalizer<'a> {
    table: &'a TypeStorage,
    /// Owned arena for interning all canonicalized OutputTy nodes.
    arena: TypeArena,
    /// Cache stores `TyRef` (arena index) so that multiple parents
    /// referencing the same (TyId, Polarity) share a single index instead
    /// of each getting a duplicated OutputTy tree. This preserves DAG
    /// structure from the bounds graph in the output, preventing the
    /// exponential tree blowup that caused OOM on files like
    /// initial-packages.nix (560K cache entries, 11+ GB RSS).
    cache: FxHashMap<(TyId, Polarity), TyRef>,
    in_progress: FxHashSet<(TyId, Polarity)>,
    /// Optional deadline for canonicalization. When exceeded, remaining
    /// types degrade to TyVar (same as inference deadline_exceeded).
    deadline: Option<Instant>,
    /// Operation counter for periodic deadline checks.
    op_counter: u32,
    /// Set when a deadline check fires. Once set, canonicalize() returns
    /// TyVar immediately for all subsequent calls.
    deadline_exceeded: bool,
}

impl<'a> Canonicalizer<'a> {
    fn new(table: &'a TypeStorage) -> Self {
        Self {
            table,
            arena: TypeArena::new(),
            cache: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            deadline: None,
            op_counter: 0,
            deadline_exceeded: false,
        }
    }

    fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Canonicalize and return an arena-interned TyRef. When the same
    /// (TyId, Polarity) is used as a child from multiple parents, they
    /// share the same index — preserving DAG structure in the output.
    ///
    /// Use this when building TyRef children (Lambda params, List elems,
    /// AttrSet fields, Named inners). Use `canonicalize` when you need
    /// an owned OutputTy for normalization (flatten, filter, etc.).
    fn canonicalize_child(&mut self, ty_id: TyId, polarity: Polarity) -> TyRef {
        // Fast path: if deadline already exceeded, return degraded type.
        if self.deadline_exceeded {
            return self.arena.intern(OutputTy::TyVar(ty_id.0));
        }

        // Periodic deadline check.
        if self.deadline.is_some() {
            self.op_counter += 1;
            if self
                .op_counter
                .is_multiple_of(CANON_DEADLINE_CHECK_INTERVAL)
                && self.deadline.is_some_and(|d| Instant::now() > d)
            {
                log::warn!("canonicalization deadline exceeded, degrading remaining types");
                self.deadline_exceeded = true;
                return self.arena.intern(OutputTy::TyVar(ty_id.0));
            }
        }

        let key = (ty_id, polarity);

        if let Some(&cached) = self.cache.get(&key) {
            return cached; // TyRef is Copy — O(1)
        }

        if self.in_progress.contains(&key) {
            return self.arena.intern(OutputTy::TyVar(ty_id.0));
        }

        // Guard against stack overflow on deeply nested type graphs.
        // canonicalize_child is the single recursive entry point —
        // expand_bounds, canonicalize_inner, and canonicalize_concrete
        // all recurse through here.
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            self.in_progress.insert(key);
            let result = self.canonicalize_inner(ty_id, polarity);
            self.in_progress.remove(&key);

            let tyref = self.arena.intern(result);
            self.cache.insert(key, tyref);
            tyref
        })
    }

    /// Canonicalize and return an owned OutputTy. Looks up the arena-interned
    /// result from `canonicalize_child`. Use this when you need to
    /// inspect/transform the result (normalization helpers, expand_bounds
    /// pipeline).
    fn canonicalize(&mut self, ty_id: TyId, polarity: Polarity) -> OutputTy {
        let tyref = self.canonicalize_child(ty_id, polarity);
        self.arena[tyref].clone()
    }

    fn canonicalize_inner(&mut self, ty_id: TyId, polarity: Polarity) -> OutputTy {
        // Clone only the data we need: for variables, just the relevant bounds
        // Vec (Vec<TyId> ~ Vec<u32>, cheap); for concrete types, the Ty value.
        // This avoids cloning the unused bounds Vec for variables.
        if let Some(v) = self.table.get_var(ty_id) {
            // Check if any bound (either polarity) is a concrete Named type.
            // Named bounds are injected by apply_type_annotation /
            // propagate_annotation_bounds for display purposes. Named bounds
            // survive extrusion (they flow through link_extruded_var). Alias
            // display is polarity-agnostic, so check both lower and upper bounds.
            let named_bound = v
                .lower_bounds
                .iter()
                .chain(v.upper_bounds.iter())
                .copied()
                .find(|&b| matches!(self.table.get(b), TypeEntry::Concrete(Ty::Named(..))));

            if let Some(named_id) = named_bound {
                // Canonicalize through the Named entry directly. This
                // produces OutputTy::Named(name, canonicalize(inner)).
                return self.canonicalize(named_id, polarity);
            }

            let bounds = match polarity {
                Positive => v.lower_bounds.clone(),
                Negative => v.upper_bounds.clone(),
            };
            self.expand_bounds(&bounds, ty_id, polarity)
        } else {
            let ty = match self.table.get(ty_id) {
                TypeEntry::Concrete(ty) => ty.clone(),
                _ => unreachable!(),
            };
            self.canonicalize_concrete(&ty, polarity)
        }
    }

    /// Expand bounds of a variable into a union (positive) or intersection (negative).
    ///
    /// Shared logic for both polarities:
    /// 1. Canonicalize each bound at the given polarity
    /// 2. Flatten nested composites (union or intersection)
    /// 3. Filter bare TyVar and Bottom members
    /// 4. Normalize: tautology removal (positive) or attrset merging + contradiction
    ///    detection (negative)
    /// 5. Build result: single element, or Union/Intersection wrapper
    ///
    /// In positive position with no concrete lower bounds, a display heuristic
    /// checks for atom-only upper bounds — `ret <: Number` becomes `number`
    /// rather than a bare type variable.
    fn expand_bounds(&mut self, bounds: &[TyId], var_id: TyId, polarity: Polarity) -> OutputTy {
        // 0. Dedup TyId bounds before canonicalization. Different TyIds can
        //    canonicalize to the same OutputTy, but duplicate TyIds always do.
        //    Deduping here (cheap u32 comparison) is much faster than deduping
        //    OutputTy values later (structural tree comparison). The bounds
        //    lists are usually small and mostly pre-deduped by compact_scc_graph,
        //    but infer_root can add duplicates after the last compact pass.
        let bounds = if bounds.len() > 16 {
            let mut seen = FxHashSet::with_capacity_and_hasher(bounds.len(), Default::default());
            let deduped: Vec<TyId> = bounds
                .iter()
                .copied()
                .filter(|id| seen.insert(*id))
                .collect();
            deduped
        } else {
            bounds.to_vec()
        };
        let bounds = &bounds;

        // 1. Canonicalize each bound at the given polarity.
        // `bounds` is a slice from the caller's local variable (already cloned
        // from storage), so no borrow conflict with `&mut self`.
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, polarity))
            .collect();

        // 2. Flatten nested composites.
        let flattened = match polarity {
            Positive => flatten_union(&self.arena, members),
            Negative => flatten_intersection(&self.arena, members),
        };

        // 3. Filter bare TyVar (uninformative in either position), Bottom
        //    (identity for union), and Top (identity for intersection).
        let concrete: Vec<OutputTy> = flattened
            .into_iter()
            .filter(|m| !matches!(m, OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top))
            .collect();

        // 4. Polarity-specific normalization.
        let had_concrete = !concrete.is_empty();
        let concrete = match polarity {
            Positive => {
                // Tautology detection: A ∨ ¬A = ⊤, drop both.
                let concrete = remove_tautological_pairs(&self.arena, concrete);
                // Absorb open attrsets subsumed by more general open attrsets.
                absorb_subsumed_union_members(concrete)
            }
            Negative => {
                // Merge multiple attrsets into one (intersection of records =
                // record with all fields).
                let concrete = merge_attrset_intersection(&mut self.arena, concrete);
                // Remove redundant negations: when an intersection contains a
                // concrete type T and Neg(S) where T and S are provably disjoint,
                // the negation adds no information. E.g. `{name: string} & ~null`
                // simplifies to `{name: string}` because attrsets are inherently
                // non-null. Only removes when the positive member has a known
                // constructor (not a TyVar).
                let concrete = remove_redundant_negations(&self.arena, concrete);
                // Contradiction detection: T ∧ ¬S = ⊥ when T ⊆ S.
                if has_type_contradiction(&self.arena, &concrete) {
                    return OutputTy::Bottom;
                }
                // Factor shared members from intersections of unions:
                // (A|C) & (B|C) = C | (A&B).
                factor_shared_from_intersection(&mut self.arena, concrete)
            }
        };

        // 5. Build the result.
        match concrete.len() {
            0 if had_concrete && polarity == Positive => {
                // Tautology removal emptied the vec — all concrete members
                // cancelled out (e.g. int | ~int). This is Top (any value).
                OutputTy::Top
            }
            0 => self.expand_bounds_empty_fallback(var_id, polarity),
            1 => concrete.into_iter().next().unwrap(),
            _ => match polarity {
                Positive => OutputTy::Union(
                    concrete
                        .into_iter()
                        .map(|ty| self.arena.intern(ty))
                        .collect(),
                ),
                Negative => OutputTy::Intersection(
                    concrete
                        .into_iter()
                        .map(|ty| self.arena.intern(ty))
                        .collect(),
                ),
            },
        }
    }

    /// Fallback when a variable has no concrete bounds in the given polarity.
    ///
    /// - **Positive**: check for atom-only upper bounds (primitives, negations of
    ///   primitives) as a display heuristic. `ret <: Number` becomes `number`
    ///   rather than a bare type variable. If no atom uppers, return TyVar.
    /// - **Negative**: if lower bounds exist (e.g. from a stub-declared union),
    ///   expand them at positive polarity. Unlike positive, all lower bounds are
    ///   used (not just atoms) because they represent explicitly declared types.
    ///   If no lower bounds, return a bare TyVar.
    fn expand_bounds_empty_fallback(&mut self, var_id: TyId, polarity: Polarity) -> OutputTy {
        if polarity == Negative {
            // When a variable in negative position (e.g. a function parameter) has
            // no upper bounds but does have lower bounds, those lower bounds
            // represent the declared type flowing in (typically from a stub like
            // `(int | string) -> bool` or `({name: string, ...} | ...) -> Derivation`).
            // Expand them at positive polarity to produce the declared union.
            //
            // This only fires when upper bounds are empty (no body usage constraints),
            // so genuinely generic params (like `x` in `x -> x`) still return TyVar
            // since both bounds are empty.
            if let Some(v) = self.table.get_var(var_id) {
                if !v.lower_bounds.is_empty() {
                    let lower = v.lower_bounds.clone();
                    return self.expand_bounds(&lower, var_id, Positive);
                }
            }
            return OutputTy::TyVar(var_id.0);
        }

        // Positive position: look for atom-only upper bounds.
        if let Some(v) = self.table.get_var(var_id) {
            let atom_uppers: Vec<TyId> = v
                .upper_bounds
                .iter()
                .copied()
                .filter(|&ub| match self.table.get(ub) {
                    TypeEntry::Concrete(Ty::Primitive(_)) => true,
                    TypeEntry::Concrete(Ty::Neg(inner)) => {
                        matches!(
                            self.table.get(*inner),
                            TypeEntry::Concrete(Ty::Primitive(_))
                        )
                    }
                    _ => false,
                })
                .collect();
            if !atom_uppers.is_empty() {
                return self.expand_bounds(&atom_uppers, var_id, Negative);
            }
        }
        OutputTy::TyVar(var_id.0)
    }

    fn canonicalize_concrete(&mut self, ty: &Ty<TyId>, polarity: Polarity) -> OutputTy {
        match ty {
            Ty::Primitive(p) => OutputTy::Primitive(*p),
            Ty::TyVar(x) => OutputTy::TyVar(*x),
            // Structural children use canonicalize_child to get shared TyRefs.
            Ty::List(elem) => OutputTy::List(self.canonicalize_child(*elem, polarity)),
            Ty::Lambda { param, body } => {
                let c_param = self.canonicalize_child(*param, polarity.flip());
                let c_body = self.canonicalize_child(*body, polarity);
                OutputTy::Lambda {
                    param: c_param,
                    body: c_body,
                }
            }
            Ty::AttrSet(attr) => {
                let mut new_fields = BTreeMap::new();
                for (k, &v) in &attr.fields {
                    new_fields.insert(k.clone(), self.canonicalize_child(v, polarity));
                }
                let dyn_ty = attr.dyn_ty.map(|d| self.canonicalize_child(d, polarity));
                OutputTy::AttrSet(AttrSetTy {
                    fields: new_fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            // Negation flips polarity: ¬T in positive position means T
            // appears in negative position (and vice versa). After
            // canonicalization the inner type may be a Union or Intersection
            // (from variable bound expansion), so we normalize via De Morgan.
            Ty::Neg(inner) => {
                let c_inner = self.canonicalize(*inner, polarity.flip());
                negate_output_ty(&mut self.arena, c_inner)
            }

            // Named: canonicalize the inner type and wrap in OutputTy::Named.
            Ty::Named(name, inner) => {
                OutputTy::Named(name.clone(), self.canonicalize_child(*inner, polarity))
            }

            // Frozen: zero-copy reference to the external arena.
            Ty::Frozen(owned) => OutputTy::Extern(owned.clone()),

            // Intersection: canonicalize both members and flatten/normalize
            // using the same logic as variable bound expansion.
            Ty::Inter(a, b) => {
                let ca = self.canonicalize(*a, polarity);
                let cb = self.canonicalize(*b, polarity);
                let members = flatten_intersection(&self.arena, vec![ca, cb]);
                // Filter bare TyVar, Bottom, and Top. Keep all members
                // around for fallback if every concrete member is filtered out.
                let all_members = members.clone();
                let concrete: Vec<OutputTy> = members
                    .into_iter()
                    .filter(|m| !matches!(m, OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top))
                    .collect();
                // Check for contradictions in all polarities for Inter types.
                // Unlike variable-bound intersections (negative polarity only),
                // Inter types from narrowing can appear in either polarity and
                // may contain contradictions like String ∧ Int = ⊥.
                if has_type_contradiction(&self.arena, &concrete) {
                    return OutputTy::Bottom;
                }
                let had_concrete = !concrete.is_empty();
                let concrete = match polarity {
                    Positive => {
                        let c = remove_redundant_negations(&self.arena, concrete);
                        remove_tautological_pairs(&self.arena, c)
                    }
                    Negative => {
                        let c = merge_attrset_intersection(&mut self.arena, concrete);
                        remove_redundant_negations(&self.arena, c)
                    }
                };
                // Factor shared members from intersections of unions:
                // (A|C) & (B|C) = C | (A&B).
                let concrete = factor_shared_from_intersection(&mut self.arena, concrete);
                match concrete.len() {
                    // Tautology removal emptied a non-empty vec in positive
                    // position — return Top.
                    0 if had_concrete && polarity == Positive => OutputTy::Top,
                    // All concrete members were filtered out. Fall back to
                    // the first member before filtering (a TyVar or Bottom).
                    0 => all_members.into_iter().next().unwrap_or(OutputTy::Bottom),
                    1 => concrete.into_iter().next().unwrap(),
                    _ => OutputTy::Intersection(
                        concrete
                            .into_iter()
                            .map(|ty| self.arena.intern(ty))
                            .collect(),
                    ),
                }
            }

            // Union: canonicalize both members and flatten/normalize.
            Ty::Union(a, b) => {
                let ca = self.canonicalize(*a, polarity);
                let cb = self.canonicalize(*b, polarity);
                let members = flatten_union(&self.arena, vec![ca, cb]);
                let all_members = members.clone();
                let concrete: Vec<OutputTy> = members
                    .into_iter()
                    .filter(|m| !matches!(m, OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top))
                    .collect();
                let had_concrete = !concrete.is_empty();
                let concrete = match polarity {
                    Positive => {
                        let c = remove_tautological_pairs(&self.arena, concrete);
                        absorb_subsumed_union_members(c)
                    }
                    Negative => absorb_subsumed_union_members(concrete),
                };
                match concrete.len() {
                    // Tautology removal emptied a non-empty vec in positive
                    // position — return Top.
                    0 if had_concrete && polarity == Positive => OutputTy::Top,
                    0 => all_members.into_iter().next().unwrap_or(OutputTy::Bottom),
                    1 => concrete.into_iter().next().unwrap(),
                    _ => OutputTy::Union(
                        concrete
                            .into_iter()
                            .map(|ty| self.arena.intern(ty))
                            .collect(),
                    ),
                }
            }
        }
    }
}

/// Canonicalize a TyId into an OutputTy using only a TypeStorage reference.
/// This captures the type's canonical form at the current moment — before
/// use-site extrusions add concrete bounds back onto polymorphic variables.
pub fn canonicalize_standalone(
    table: &TypeStorage,
    ty_id: TyId,
    polarity: Polarity,
) -> (TypeArena, TyRef) {
    canonicalize_standalone_with_deadline(table, ty_id, polarity, None)
}

pub fn canonicalize_standalone_with_deadline(
    table: &TypeStorage,
    ty_id: TyId,
    polarity: Polarity,
    deadline: Option<Instant>,
) -> (TypeArena, TyRef) {
    let mut canon = Canonicalizer::new(table);
    if let Some(d) = deadline {
        canon = canon.with_deadline(d);
    }
    let ty = canon.canonicalize_child(ty_id, polarity);
    (canon.arena, ty)
}

// ==============================================================================
// Shared helpers
// ==============================================================================

/// Negate an OutputTy, applying normalization rules:
///
/// 1. `¬(¬A)`        → `A`                              (double negation)
/// 2. `¬(A ∨ B ∨ …)` → `¬A ∧ ¬B ∧ …`                   (De Morgan)
/// 3. `¬(A ∧ B ∧ …)` → `¬A ∨ ¬B ∨ …`                   (De Morgan)
/// 4. Anything else   → `Neg(inner)`                     (wrap as-is)
///
/// Recurses on each member so nested structures are fully normalized.
/// Uses a for loop instead of `.map()` to avoid closure borrow issues
/// with the mutable arena reference.
fn negate_output_ty(arena: &mut TypeArena, inner: OutputTy) -> OutputTy {
    // Guard against stack overflow on deeply nested Union/Intersection trees
    // (De Morgan expansion recurses independently of canonicalize).
    stacker::maybe_grow(256 * 1024, 1024 * 1024, || match inner {
        // ¬(¬A) → A
        OutputTy::Neg(a) => arena[a].clone(),

        // ¬(A ∨ B ∨ …) → ¬A ∧ ¬B ∧ …
        OutputTy::Union(members) => {
            let mut new_members = Vec::with_capacity(members.len());
            for m in members {
                let child = arena[m].clone();
                let negated = negate_output_ty(arena, child);
                new_members.push(arena.intern(negated));
            }
            OutputTy::Intersection(new_members)
        }

        // ¬(A ∧ B ∧ …) → ¬A ∨ ¬B ∨ …
        OutputTy::Intersection(members) => {
            let mut new_members = Vec::with_capacity(members.len());
            for m in members {
                let child = arena[m].clone();
                let negated = negate_output_ty(arena, child);
                new_members.push(arena.intern(negated));
            }
            OutputTy::Union(new_members)
        }

        // Leaf or compound type that isn't union/intersection/neg — just wrap.
        other => OutputTy::Neg(arena.intern(other)),
    })
}

/// Remove tautological pairs from a union: `T ∨ ¬T` = ⊤.
/// When both a type and its negation appear, both are dropped since their
/// union is the top type and adds no information to the overall union.
///
/// Handles all constructor kinds — primitives, attrsets, lists, lambdas — by
/// checking structural equality between positive members and negated members.
/// For primitives, also handles subtype tautologies (Int ∨ ¬Int).
fn remove_tautological_pairs(arena: &TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    // Collect negated inner types (looked up from the arena).
    let negated_inner_refs: Vec<TyRef> = members
        .iter()
        .filter_map(|m| match m {
            OutputTy::Neg(inner) => Some(*inner),
            _ => None,
        })
        .collect();
    let negated_inners: Vec<&OutputTy> = negated_inner_refs.iter().map(|&r| &arena[r]).collect();

    if negated_inners.is_empty() {
        return members;
    }

    // Collect positive (non-negated, non-TyVar, non-Bottom, non-Top) members.
    let positives: Vec<&OutputTy> = members
        .iter()
        .filter(|m| {
            !matches!(
                m,
                OutputTy::Neg(_) | OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top
            )
        })
        .collect();

    // Find tautological pairs: a positive member whose negation also appears.
    // T ∨ ¬T = ⊤ when T and the negated inner are structurally equal.
    let mut tautological_positives: SmallVec<[usize; 8]> = SmallVec::new();
    let mut tautological_negatives: SmallVec<[usize; 8]> = SmallVec::new();

    for (pi, pos) in positives.iter().enumerate() {
        for (ni, neg_inner) in negated_inners.iter().enumerate() {
            if pos == neg_inner {
                if !tautological_positives.contains(&pi) {
                    tautological_positives.push(pi);
                }
                if !tautological_negatives.contains(&ni) {
                    tautological_negatives.push(ni);
                }
            }
        }
    }

    if tautological_positives.is_empty() {
        return members;
    }

    // Remove both T and ¬T for each tautological pair.
    let mut pos_idx = 0;
    let mut neg_idx = 0;
    members
        .into_iter()
        .filter(|m| match m {
            OutputTy::Neg(_) => {
                let keep = !tautological_negatives.contains(&neg_idx);
                neg_idx += 1;
                keep
            }
            OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top => true,
            _ => {
                let keep = !tautological_positives.contains(&pos_idx);
                pos_idx += 1;
                keep
            }
        })
        .collect()
}

/// Absorb subsumed attrsets in a union. In a union `A | B`, open attrset A
/// subsumes open attrset B when:
/// - Both are open
/// - A has no dyn_ty (or A.dyn_ty == B.dyn_ty)
/// - Every required (non-optional) field of A also appears in B
///
/// This is exact: `A | B = A` when `B <: A` structurally. The common case is
/// `{ ... }` (open, no fields) absorbing any open attrset. Closed attrsets
/// are never absorbed because they assert "exactly these fields".
fn absorb_subsumed_union_members(members: Vec<OutputTy>) -> Vec<OutputTy> {
    // Collect indices of attrset members for pairwise comparison.
    let attrset_indices: SmallVec<[usize; 8]> = members
        .iter()
        .enumerate()
        .filter_map(|(i, m)| matches!(m, OutputTy::AttrSet(_)).then_some(i))
        .collect();

    if attrset_indices.len() < 2 {
        return members;
    }

    // Mark indices that are subsumed by another attrset in the union.
    // SmallVec for small N (typically 2-4 attrsets in a union).
    let mut subsumed: SmallVec<[usize; 8]> = SmallVec::new();
    for &i in &attrset_indices {
        if subsumed.contains(&i) {
            continue;
        }
        for &j in &attrset_indices {
            if i == j || subsumed.contains(&j) {
                continue;
            }
            let a = match &members[i] {
                OutputTy::AttrSet(a) => a,
                _ => unreachable!(),
            };
            let b = match &members[j] {
                OutputTy::AttrSet(b) => b,
                _ => unreachable!(),
            };
            // A subsumes B when B <: A:
            // - Both open (closed attrsets assert exact fields)
            // - A has no dyn_ty or same dyn_ty as B
            // - Every required field of A appears in B
            if a.open
                && b.open
                && (a.dyn_ty.is_none() || a.dyn_ty == b.dyn_ty)
                && a.fields
                    .keys()
                    .all(|k| a.optional_fields.contains(k) || b.fields.contains_key(k))
            {
                // B is more specific than A, so A absorbs B.
                subsumed.push(j);
            }
        }
    }

    if subsumed.is_empty() {
        return members;
    }

    members
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !subsumed.contains(i))
        .map(|(_, m)| m)
        .collect()
}

/// Factor shared members from an intersection of unions using the distributive law:
/// `(A|C) & (B|C) = C | (A&B)`.
///
/// When intersection members are unions sharing common OutputTy members,
/// the shared members are factored out. For example, if `string` appears in
/// every union term, it gets extracted: `(string|X) & (string|Y) = string | (X&Y)`.
///
/// Algorithm:
/// 1. Partition intersection members into unions and non-unions
/// 2. If < 2 union members, return as-is (nothing to factor)
/// 3. Find OutputTy members present in ALL unions (set intersection)
/// 4. Remove shared members from each union, producing remainders
/// 5. Return `Union(shared..., Intersection(remainders..., non_unions...))`
fn factor_shared_from_intersection(arena: &mut TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut unions: SmallVec<[SmallVec<[OutputTy; 8]>; 4]> = SmallVec::new();
    let mut non_unions: SmallVec<[OutputTy; 8]> = SmallVec::new();

    for m in members {
        match m {
            OutputTy::Union(inner) => {
                unions.push(inner.into_iter().map(|r| arena[r].clone()).collect());
            }
            other => non_unions.push(other),
        }
    }

    if unions.len() < 2 {
        // Reassemble: put unions back as OutputTy::Union members alongside non-unions.
        let mut result = non_unions;
        for u in unions {
            match u.len() {
                0 => {}
                1 => result.push(u.into_iter().next().unwrap()),
                _ => result.push(OutputTy::Union(
                    u.into_iter().map(|ty| arena.intern(ty)).collect(),
                )),
            }
        }
        return result.into_vec();
    }

    // Find members present in ALL unions. Linear scan since N is typically 2-8.
    let mut shared: SmallVec<[OutputTy; 8]> = unions[0].clone();
    for u in &unions[1..] {
        shared.retain(|m| u.contains(m));
    }

    if shared.is_empty() {
        // No shared members — reassemble unchanged.
        let mut result = non_unions;
        for u in unions {
            result.push(OutputTy::Union(
                u.into_iter().map(|ty| arena.intern(ty)).collect(),
            ));
        }
        return result.into_vec();
    }

    // Remove shared members from each union, producing remainders.
    let remainders: SmallVec<[OutputTy; 8]> = unions
        .into_iter()
        .filter_map(|u| {
            let remainder: SmallVec<[OutputTy; 8]> =
                u.into_iter().filter(|m| !shared.contains(m)).collect();
            match remainder.len() {
                0 => None,
                1 => Some(remainder.into_iter().next().unwrap()),
                _ => Some(OutputTy::Union(
                    remainder.into_iter().map(|ty| arena.intern(ty)).collect(),
                )),
            }
        })
        .collect();

    // Build the factored result: shared | (remainders & non_unions)
    let mut shared_vec: SmallVec<[OutputTy; 8]> = shared;
    shared_vec.sort();

    // Build the intersection of remainders + non_unions.
    let mut intersection_parts: SmallVec<[OutputTy; 8]> = remainders;
    intersection_parts.extend(non_unions);

    if intersection_parts.is_empty() {
        // All union members were shared — result is just the shared union.
        match shared_vec.len() {
            1 => vec![shared_vec.into_iter().next().unwrap()],
            _ => vec![OutputTy::Union(
                shared_vec.into_iter().map(|ty| arena.intern(ty)).collect(),
            )],
        }
    } else {
        // Result is shared | intersection(remainders, non_unions).
        let intersection = match intersection_parts.len() {
            1 => intersection_parts.into_iter().next().unwrap(),
            _ => OutputTy::Intersection(
                intersection_parts
                    .into_iter()
                    .map(|ty| arena.intern(ty))
                    .collect(),
            ),
        };
        shared_vec.push(intersection);
        // Return as a single-element vec containing the final Union.
        // The caller (expand_bounds/canonicalize_concrete) will wrap in
        // Intersection if there are multiple members, but we've already
        // restructured into a Union, so return it as one element.
        vec![OutputTy::Union(
            shared_vec.into_iter().map(|ty| arena.intern(ty)).collect(),
        )]
    }
}

/// Check whether an intersection contains a contradictory pair.
///
/// Two kinds of contradictions:
/// 1. `T ∧ ¬S` where `T <: S` (subsumption). E.g. `Int ∧ ¬Number = ⊥`
///    because every Int is a Number. Note: `Number ∧ ¬Int` is NOT a
///    contradiction — Number includes Float, which is not Int.
/// 2. `T ∧ S` where `T` and `S` are provably disjoint. E.g. `Int ∧ String = ⊥`.
///
/// Examples:
/// - `int & ~int` → contradiction (Int <: Int, reflexive)
/// - `int & ~number` → contradiction (Int <: Number)
/// - `{name: string} & ~{name: string}` → contradiction (structural equality)
/// - `number & ~int` → NOT a contradiction (Number ⊄ Int)
/// - `int & ~null` → NOT a contradiction (disjoint, handled by redundant neg removal)
fn has_type_contradiction(arena: &TypeArena, members: &[OutputTy]) -> bool {
    // Collect positive (non-negated) and negated inner types.
    let mut positives: SmallVec<[&OutputTy; 8]> = SmallVec::new();
    let mut negated_inners: SmallVec<[&OutputTy; 8]> = SmallVec::new();

    for m in members {
        match m {
            OutputTy::Neg(inner) => negated_inners.push(&arena[*inner]),
            OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top => {}
            other => positives.push(other),
        }
    }

    // A contradiction exists when a positive type is a subtype of (or equal
    // to) a negated type: T ∧ ¬S = ⊥ iff T <: S. The previous check used
    // "not disjoint" which conflated overlap with subsumption — e.g. it would
    // incorrectly flag `Number ∧ ¬Int` as contradictory.
    for pos in &positives {
        for neg in &negated_inners {
            if is_output_subtype_or_equal(pos, neg) {
                return true;
            }
        }
    }

    // Also check for mutually disjoint positives: String ∧ Int = ⊥
    // because String and Int have no overlap.
    //
    // Optimization: disjointness is determined by constructor shape (Primitive,
    // AttrSet, List, Lambda, Opaque). Two non-primitive types with the same
    // shape are never disjoint, so if all positives share one non-primitive
    // shape, skip the O(n²) pairwise check entirely. This matters for files
    // like hackage-packages.nix where callPackage creates 19K+ Lambda
    // intersection members — all same shape, zero disjoint pairs.
    if positives.len() > 1 {
        let all_same_non_primitive = positives
            .windows(2)
            .all(|w| std::mem::discriminant(w[0]) == std::mem::discriminant(w[1]))
            && !matches!(positives[0], OutputTy::Primitive(_));

        if !all_same_non_primitive {
            for i in 0..positives.len() {
                for j in (i + 1)..positives.len() {
                    if are_output_types_disjoint(positives[i], positives[j]) {
                        return true;
                    }
                }
            }
        }
    }

    false
}

/// Check whether `sub` is a subtype of (or structurally equal to) `sup` in the
/// OutputTy representation. This is a conservative approximation — it returns
/// true only when the relationship is provable from constructor shape alone.
///
/// Used by `has_type_contradiction` to determine whether `T ∧ ¬S = ⊥`.
///
/// Handles:
/// - Primitive subtyping: `Int <: Number`, `Float <: Number`
/// - Structural equality for compound types (attrsets, lists, lambdas)
/// - Different constructors → not a subtype
fn is_output_subtype_or_equal(sub: &OutputTy, sup: &OutputTy) -> bool {
    match (sub, sup) {
        (OutputTy::Primitive(p1), OutputTy::Primitive(p2)) => p1 == p2 || p1.is_subtype_of(p2),
        // Same structural compound types → equal (conservative).
        (a, b) if a == b => true,
        // Different constructors or non-trivially-comparable → not a subtype.
        _ => false,
    }
}

/// Check whether two OutputTy values are provably disjoint (their intersection
/// is uninhabited). Delegates to the shared `are_shapes_disjoint` logic in
/// `lang_ty::disjoint`.
///
/// See `lang_ty::disjoint::are_shapes_disjoint` for the full disjointness rules.
fn are_output_types_disjoint(a: &OutputTy, b: &OutputTy) -> bool {
    // Collect field keys as sorted slices — avoids building a throwaway
    // BTreeMap<SmolStr, ()> just to check key membership.
    let a_keys: SmallVec<[SmolStr; 8]>;
    let b_keys: SmallVec<[SmolStr; 8]>;

    let a_shape = match a {
        OutputTy::Primitive(p) => ConstructorShape::Primitive(*p),
        OutputTy::AttrSet(attr) => {
            a_keys = attr.fields.keys().cloned().collect();
            ConstructorShape::AttrSet {
                field_keys: &a_keys,
                open: attr.open,
                optional: &attr.optional_fields,
            }
        }
        OutputTy::List(_) => ConstructorShape::List,
        OutputTy::Lambda { .. } => ConstructorShape::Lambda,
        _ => ConstructorShape::Opaque,
    };

    let b_shape = match b {
        OutputTy::Primitive(p) => ConstructorShape::Primitive(*p),
        OutputTy::AttrSet(attr) => {
            b_keys = attr.fields.keys().cloned().collect();
            ConstructorShape::AttrSet {
                field_keys: &b_keys,
                open: attr.open,
                optional: &attr.optional_fields,
            }
        }
        OutputTy::List(_) => ConstructorShape::List,
        OutputTy::Lambda { .. } => ConstructorShape::Lambda,
        _ => ConstructorShape::Opaque,
    };

    are_shapes_disjoint(&a_shape, &b_shape)
}

/// Remove redundant negations from an intersection. When the intersection
/// contains a positive type `T` with a known constructor and `Neg(S)` where
/// `T` and `S` are provably disjoint, the negation is redundant because `T`
/// can never be `S` anyway.
///
/// Examples:
/// - `{name: string} & ~null` → `{name: string}` (attrset ≠ null)
/// - `[int] & ~string` → `[int]` (list ≠ string)
/// - `number & ~null` → `number` (number ≠ null)
///
/// Does NOT remove when the only positive members are TyVars — `a & ~null`
/// stays as-is because `a` could be null.
fn remove_redundant_negations(arena: &TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    // Check for positive members with known constructors (not TyVar/Bottom/Neg).
    // Use indices to avoid cloning — are_output_types_disjoint takes references.
    let has_concrete = members.iter().any(|m| {
        matches!(
            m,
            OutputTy::Primitive(_)
                | OutputTy::AttrSet(_)
                | OutputTy::List(_)
                | OutputTy::Lambda { .. }
        )
    });

    if !has_concrete {
        return members;
    }

    // Collect indices of concrete positive members to avoid cloning.
    let concrete_indices: SmallVec<[usize; 8]> = members
        .iter()
        .enumerate()
        .filter_map(|(i, m)| {
            matches!(
                m,
                OutputTy::Primitive(_)
                    | OutputTy::AttrSet(_)
                    | OutputTy::List(_)
                    | OutputTy::Lambda { .. }
            )
            .then_some(i)
        })
        .collect();

    // Determine which members to keep. We can't filter in-place because the
    // filter closure needs to reference members by index.
    let keep: SmallVec<[bool; 16]> = members
        .iter()
        .map(|m| {
            if let OutputTy::Neg(inner) = m {
                // Keep this negation only if it's NOT disjoint from all concrete
                // positives. If it IS disjoint from every positive, it's redundant.
                !concrete_indices
                    .iter()
                    .all(|&i| are_output_types_disjoint(&members[i], &arena[*inner]))
            } else {
                true
            }
        })
        .collect();

    members
        .into_iter()
        .zip(keep)
        .filter_map(|(m, k)| k.then_some(m))
        .collect()
}

/// Flatten a nested composite type (union or intersection) and deduplicate members.
/// `extract_nested` returns the inner members if the OutputTy is the matching
/// composite variant (Union or Intersection), or None for other variants.
/// Uses structural equality (not normalize_vars) so that distinct type variables
/// are preserved even if they'd normalize to the same index.
fn flatten_composite(
    arena: &TypeArena,
    members: Vec<OutputTy>,
    extract_nested: fn(&OutputTy) -> Option<&Vec<TyRef>>,
) -> Vec<OutputTy> {
    // Fast path: when no member is a nested composite, flattening is a no-op.
    // With large member counts (e.g. hackage-packages.nix: 19K+ intersection
    // members from callPackage), the linear contains() dedup becomes O(n²)
    // and dominates inference time. Since expand_bounds already TyId-dedups
    // its bounds, duplicates in the non-flattened case are rare (only when
    // different TyIds canonicalize to structurally equal OutputTy), so we
    // can safely skip the expensive OutputTy-level dedup for large N.
    let needs_flatten = members.iter().any(|m| extract_nested(m).is_some());
    if !needs_flatten && members.len() > 64 {
        return members;
    }

    let mut result: SmallVec<[OutputTy; 8]> = SmallVec::new();
    for m in members {
        if let Some(inner) = extract_nested(&m) {
            for &sub in inner {
                // Look up the child OutputTy from the arena.
                let child = &arena[sub];
                // Linear contains() is faster than HashSet for N typically 2-8.
                if !result.contains(child) {
                    result.push(child.clone());
                }
            }
        } else if !result.contains(&m) {
            result.push(m);
        }
    }
    result.into_vec()
}

fn flatten_union(arena: &TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    flatten_composite(arena, members, |ty| match ty {
        OutputTy::Union(inner) => Some(inner),
        _ => None,
    })
}

fn flatten_intersection(arena: &TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    flatten_composite(arena, members, |ty| match ty {
        OutputTy::Intersection(inner) => Some(inner),
        _ => None,
    })
}

/// Merge multiple attrsets in an intersection into a single attrset.
/// The intersection of `{ foo: int }` and `{ bar: string }` is `{ foo: int, bar: string }`.
/// For overlapping fields, the field types are intersected.
fn merge_attrset_intersection(arena: &mut TypeArena, members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut attrsets: SmallVec<[AttrSetTy<TyRef>; 4]> = SmallVec::new();
    let mut others: SmallVec<[OutputTy; 8]> = SmallVec::new();

    for m in members {
        match m {
            OutputTy::AttrSet(attr) => attrsets.push(attr),
            other => others.push(other),
        }
    }

    if attrsets.is_empty() {
        return others.into_vec();
    }

    // Merge all attrsets. For overlapping fields, if both have concrete types
    // that differ, produce an Intersection for that field.
    let mut merged_fields: BTreeMap<smol_str::SmolStr, TyRef> = BTreeMap::new();
    // Intersection of attrsets is open only if ALL inputs are open: a closed
    // attrset asserts "exactly these fields", so intersecting with it closes
    // the result.
    let mut all_open = true;
    let mut merged_dyn: Option<TyRef> = None;

    for attr in &attrsets {
        all_open = all_open && attr.open;
        // Intersect dyn_ty values: if multiple attrsets have a dyn_ty, the
        // result's dyn_ty is the intersection of all of them.
        match (&merged_dyn, &attr.dyn_ty) {
            (None, Some(_)) => merged_dyn.clone_from(&attr.dyn_ty),
            (Some(existing), Some(new)) if existing != new => {
                merged_dyn = Some(arena.intern(OutputTy::Intersection(vec![*existing, *new])));
            }
            _ => {}
        }
        for (k, v) in &attr.fields {
            merged_fields
                .entry(k.clone())
                .and_modify(|existing| {
                    if matches!(arena[*existing], OutputTy::TyVar(_)) {
                        *existing = *v;
                    } else if *existing != *v {
                        *existing = arena.intern(OutputTy::Intersection(vec![*existing, *v]));
                    }
                })
                .or_insert(*v);
        }
    }

    // A field is optional in the intersection only if it's optional in ALL
    // attrsets that contain it — intersection is the most restrictive.
    let mut merged_optional: std::collections::BTreeSet<smol_str::SmolStr> =
        std::collections::BTreeSet::new();
    for key in merged_fields.keys() {
        let optional_in_all = attrsets.iter().all(|attr| {
            // If this attrset doesn't contain the field at all, it doesn't
            // constrain its optionality — skip it.
            if !attr.fields.contains_key(key) {
                return true;
            }
            attr.optional_fields.contains(key)
        });
        if optional_in_all {
            merged_optional.insert(key.clone());
        }
    }

    let merged = OutputTy::AttrSet(AttrSetTy {
        fields: merged_fields,
        dyn_ty: merged_dyn,
        open: all_open,
        optional_fields: merged_optional,
    });

    others.push(merged);
    others.into_vec()
}

// ==============================================================================
// Collector — final canonicalization pass (after all inference is complete)
// ==============================================================================

pub(crate) struct Collector<'db> {
    ctx: CheckCtx<'db>,
}

impl<'db> Collector<'db> {
    pub fn new(ctx: CheckCtx<'db>) -> Self {
        Self { ctx }
    }

    #[tracing::instrument(level = "info", skip_all, name = "canonicalize")]
    pub fn finalize_inference(&mut self) -> InferenceResult {
        let deadline_exceeded = self.ctx.deadline_exceeded;

        let name_tys: Vec<_> = self
            .ctx
            .module
            .names()
            .map(|(name, _)| {
                let ty: TyId = (u32::from(name.into_raw())).into();
                (name, ty)
            })
            .collect();

        let name_cnt = self.ctx.module.names().len();
        let expr_cnt = self.ctx.module.exprs().len();
        let mut name_ty_map = ArenaMap::with_capacity(name_cnt);
        let mut expr_ty_map = ArenaMap::with_capacity(expr_cnt);

        // Create a Canonicalizer that borrows the type storage for this pass.
        // Wire the inference deadline into canonicalization: if inference
        // already exceeded its deadline, give canonicalization a short budget
        // (500ms) for essential name-level types. Otherwise use the remaining
        // inference deadline.
        let canon_deadline = if deadline_exceeded {
            Some(Instant::now() + std::time::Duration::from_millis(500))
        } else {
            self.ctx.deadline
        };
        let mut canon = Canonicalizer::new(&self.ctx.types.storage);
        if let Some(d) = canon_deadline {
            canon = canon.with_deadline(d);
        }

        let t_names = std::time::Instant::now();
        let mut late_canon_count = 0u32;
        for (name, ty) in name_tys {
            // Prefer the early-canonicalized type (captured before use-site
            // extrusion contaminated the bounds) over late canonicalization.
            let tyref = if let Some((early_arena, early_ty)) = self.ctx.early_canonical.get(name) {
                if matches!(early_arena[*early_ty], OutputTy::TyVar(_)) {
                    // The early snapshot captured no type information (bare variable),
                    // likely because enclosing lambda parameter annotations hadn't
                    // propagated yet. Fall back to late canonicalization which sees
                    // the fully-constrained bounds — unless the deadline was exceeded,
                    // in which case use a degraded unconstrained type to avoid
                    // expensive canonicalization on degenerate type graphs.
                    if deadline_exceeded {
                        canon.arena.intern(OutputTy::TyVar(0))
                    } else {
                        late_canon_count += 1;
                        canon.canonicalize_child(ty, Positive)
                    }
                } else {
                    // Import the early-canonicalized type into the final arena.
                    let mut cache = FxHashMap::default();
                    import_from_arena(&mut canon.arena, early_arena, *early_ty, &mut cache)
                }
            } else if deadline_exceeded {
                // When the deadline was exceeded, use a degraded unconstrained type
                // for names without an early-canonical snapshot. Late canonicalization
                // can be very expensive on degenerate type graphs from partial inference.
                canon.arena.intern(OutputTy::TyVar(0))
            } else {
                late_canon_count += 1;
                canon.canonicalize_child(ty, Positive)
            };
            name_ty_map.insert(name, tyref);
        }
        let names_elapsed = t_names.elapsed();
        if names_elapsed.as_millis() > 10 {
            log::info!(
                "  name canonicalization: {:.1}ms ({} names, {} late-canon, cache: {}, RSS: {:.0}MB)",
                names_elapsed.as_secs_f64() * 1000.0,
                name_cnt,
                late_canon_count,
                canon.cache.len(),
                super::infer::rss_mb(),
            );
        }

        // When the inference deadline was exceeded, skip expression-level
        // canonicalization. It iterates over every expression in the module
        // and can be very expensive when the type graph has degenerate bounds
        // from partial inference. Name-level types (above) are sufficient for
        // hover/completion; expr-level types are mainly used for diagnostics
        // and inlay hints, which are less critical on timed-out files.
        if !deadline_exceeded {
            let t_exprs = std::time::Instant::now();
            let expr_tys: Vec<_> = self
                .ctx
                .module
                .exprs()
                .map(|(expr, _)| {
                    let ty = self.ctx.ty_for_expr(expr);
                    (expr, ty)
                })
                .collect();

            for (expr, ty) in expr_tys {
                let tyref = canon.canonicalize_child(ty, Positive);
                expr_ty_map.insert(expr, tyref);
            }
            let exprs_elapsed = t_exprs.elapsed();
            if exprs_elapsed.as_millis() > 10 {
                log::info!(
                    "  expr canonicalization: {:.1}ms ({} exprs, cache: {}, RSS: {:.0}MB)",
                    exprs_elapsed.as_secs_f64() * 1000.0,
                    expr_cnt,
                    canon.cache.len(),
                    super::infer::rss_mb(),
                );
            }
        }

        // Extract the arena from the canonicalizer and normalize vars.
        let mut arena = canon.arena;

        // Normalize type variable indices for name-level types.
        for (_, ty_ref) in name_ty_map.iter_mut() {
            *ty_ref = arena.normalize_vars(*ty_ref);
        }

        // Normalize vars for the entry expression.
        if let Some(entry_ref) = expr_ty_map.get(self.ctx.module.entry_expr) {
            let normalized = arena.normalize_vars(*entry_ref);
            expr_ty_map.insert(self.ctx.module.entry_expr, normalized);
        }

        InferenceResult {
            arena: std::sync::Arc::new(arena),
            name_ty_map,
            expr_ty_map,
        }
    }
}

// ==============================================================================
// Tests — normalization helpers
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lang_ty::{arc_ty, PrimitiveTy};

    /// Helper: create an OutputTy for a primitive without needing an arena.
    fn prim(p: PrimitiveTy) -> OutputTy {
        OutputTy::Primitive(p)
    }
    fn int() -> OutputTy {
        prim(PrimitiveTy::Int)
    }
    fn string() -> OutputTy {
        prim(PrimitiveTy::String)
    }
    fn bool_() -> OutputTy {
        prim(PrimitiveTy::Bool)
    }
    fn float() -> OutputTy {
        prim(PrimitiveTy::Float)
    }
    fn null() -> OutputTy {
        prim(PrimitiveTy::Null)
    }
    fn number() -> OutputTy {
        prim(PrimitiveTy::Number)
    }
    fn path() -> OutputTy {
        prim(PrimitiveTy::Path)
    }

    /// Helper: create an OutputTy::Neg with an arena-interned inner.
    fn neg(arena: &mut TypeArena, inner: OutputTy) -> OutputTy {
        OutputTy::Neg(arena.intern(inner))
    }

    /// Helper: create an OutputTy::Union with arena-interned members.
    fn union(arena: &mut TypeArena, members: Vec<OutputTy>) -> OutputTy {
        OutputTy::Union(members.into_iter().map(|m| arena.intern(m)).collect())
    }

    /// Helper: create an OutputTy::Intersection with arena-interned members.
    fn isect(arena: &mut TypeArena, members: Vec<OutputTy>) -> OutputTy {
        OutputTy::Intersection(members.into_iter().map(|m| arena.intern(m)).collect())
    }

    // -- negate_output_ty tests -----------------------------------------------

    #[test]
    fn negate_double_neg() {
        // ¬(¬Int) → Int
        let mut a = TypeArena::new();
        let inner = neg(&mut a, int());
        let negated = negate_output_ty(&mut a, inner);
        assert_eq!(negated, int());
    }

    #[test]
    fn negate_union_de_morgan() {
        // ¬(Int ∨ String) → ¬Int ∧ ¬String
        let mut a = TypeArena::new();
        let input = union(&mut a, vec![int(), string()]);
        let result = negate_output_ty(&mut a, input);
        let neg_int = neg(&mut a, int());
        let neg_str = neg(&mut a, string());
        let expected = isect(&mut a, vec![neg_int, neg_str]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_intersection_de_morgan() {
        // ¬(Int ∧ String) → ¬Int ∨ ¬String
        let mut a = TypeArena::new();
        let input = isect(&mut a, vec![int(), string()]);
        let result = negate_output_ty(&mut a, input);
        let neg_int = neg(&mut a, int());
        let neg_str = neg(&mut a, string());
        let expected = union(&mut a, vec![neg_int, neg_str]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_nested_de_morgan() {
        // ¬(¬Int ∨ String) → ¬(¬Int) ∧ ¬String → Int ∧ ¬String
        let mut a = TypeArena::new();
        let neg_int = neg(&mut a, int());
        let input = union(&mut a, vec![neg_int, string()]);
        let result = negate_output_ty(&mut a, input);
        let neg_str = neg(&mut a, string());
        let expected = isect(&mut a, vec![int(), neg_str]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_primitive_wraps() {
        // ¬Int → Neg(Int)
        let mut a = TypeArena::new();
        let result = negate_output_ty(&mut a, int());
        assert_eq!(result, neg(&mut a, int()));
    }

    // -- has_type_contradiction tests -------------------------------------

    #[test]
    fn contradiction_exact_match() {
        // Int ∧ ¬Int → contradiction
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, int())];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn contradiction_subtype() {
        // Int ∧ ¬Number → contradiction (Int <: Number)
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, number())];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn contradiction_float_subtype() {
        // Float ∧ ¬Number → contradiction (Float <: Number)
        let mut a = TypeArena::new();
        let members = vec![float(), neg(&mut a, number())];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn no_contradiction_different_types() {
        // Int ∧ ¬String — no contradiction
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, string())];
        assert!(!has_type_contradiction(&a, &members));
    }

    #[test]
    fn contradiction_disjoint_positives() {
        // Int ∧ String — disjoint primitives, IS a contradiction.
        let a = TypeArena::new();
        let members = vec![int(), string()];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn no_contradiction_same_positives() {
        // Int ∧ Int — same type, no contradiction.
        let a = TypeArena::new();
        let members = vec![int(), int()];
        assert!(!has_type_contradiction(&a, &members));
    }

    // -- remove_tautological_pairs tests --------------------------------------

    #[test]
    fn tautology_exact_match() {
        // Int ∨ ¬Int → empty (both removed)
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, int())];
        let result = remove_tautological_pairs(&a, members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_preserves_other_members() {
        // Int ∨ ¬Int ∨ String → String
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, int()), string()];
        let result = remove_tautological_pairs(&a, members);
        assert_eq!(result, vec![string()]);
    }

    #[test]
    fn no_tautology_different_types() {
        // Int ∨ ¬String — no tautology, kept as-is
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, string())];
        let result = remove_tautological_pairs(&a, members.clone());
        assert_eq!(result, members);
    }

    // -- contradiction canonicalization tests (G3) ----------------------------

    #[test]
    fn contradiction_canonicalizes_to_bottom() {
        // Build a type variable whose upper bounds produce `int & ~int` in
        // negative position. Returns Bottom (never) — the uninhabited type.
        use crate::storage::TypeStorage;
        use lang_ty::Ty;

        let mut table = TypeStorage::new();
        let var_id = table.new_var();
        let int_ty = table.new_concrete(Ty::Primitive(PrimitiveTy::Int));
        let neg_int = table.new_concrete(Ty::Neg(int_ty));

        // Add int and ~int as upper bounds of the variable.
        table.add_upper_bound(var_id, int_ty);
        table.add_upper_bound(var_id, neg_int);

        let (result_arena, result_ty) = canonicalize_standalone(&table, var_id, Negative);
        assert_eq!(
            result_arena[result_ty],
            OutputTy::Bottom,
            "int & ~int contradiction should produce Bottom (never), got: {:?}",
            result_arena[result_ty]
        );
    }

    #[test]
    fn no_contradiction_string_neg_null() {
        // `string & ~null` is NOT a contradiction — string and null are
        // disjoint types. The ~null is redundant (string is inherently
        // non-null) and gets removed, leaving just `string`.
        use crate::storage::TypeStorage;
        use lang_ty::Ty;

        let mut table = TypeStorage::new();
        let var_id = table.new_var();
        let string_ty = table.new_concrete(Ty::Primitive(PrimitiveTy::String));
        let null_ty = table.new_concrete(Ty::Primitive(PrimitiveTy::Null));
        let neg_null = table.new_concrete(Ty::Neg(null_ty));

        table.add_upper_bound(var_id, string_ty);
        table.add_upper_bound(var_id, neg_null);

        let (result_arena, result_ty) = canonicalize_standalone(&table, var_id, Negative);
        // ~null is redundant alongside string (disjoint constructors), so
        // it gets removed, leaving just string.
        assert_eq!(
            result_arena[result_ty],
            string(),
            "string & ~null should simplify to string, got: {:?}",
            result_arena[result_ty]
        );
    }

    // -- are_output_types_disjoint tests --------------------------------------

    #[test]
    fn disjoint_primitive_vs_primitive() {
        assert!(are_output_types_disjoint(&int(), &string()));
        assert!(are_output_types_disjoint(&null(), &bool_()));
        assert!(are_output_types_disjoint(&path(), &float()));
    }

    #[test]
    fn not_disjoint_same_primitive() {
        assert!(!are_output_types_disjoint(&int(), &int()));
        assert!(!are_output_types_disjoint(&string(), &string()));
    }

    #[test]
    fn not_disjoint_subtype_primitives() {
        // Int and Number overlap (Int <: Number).
        assert!(!are_output_types_disjoint(&int(), &number()));
        assert!(!are_output_types_disjoint(&number(), &int()));
        // Float and Number overlap (Float <: Number).
        assert!(!are_output_types_disjoint(&float(), &number()));
    }

    #[test]
    fn disjoint_primitive_vs_attrset() {
        let mut a = TypeArena::new();
        let attrset = arc_ty!(&mut a, { "name": String });
        let attrset = a[attrset].clone();
        assert!(are_output_types_disjoint(&null(), &attrset));
        assert!(are_output_types_disjoint(&attrset, &null()));
        assert!(are_output_types_disjoint(&int(), &attrset));
    }

    #[test]
    fn disjoint_primitive_vs_list() {
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        assert!(are_output_types_disjoint(&string(), &list));
        assert!(are_output_types_disjoint(&list, &string()));
    }

    #[test]
    fn disjoint_primitive_vs_lambda() {
        let mut a = TypeArena::new();
        let lambda = OutputTy::Lambda {
            param: arc_ty!(&mut a, Int),
            body: arc_ty!(&mut a, String),
        };
        assert!(are_output_types_disjoint(&null(), &lambda));
        assert!(are_output_types_disjoint(&lambda, &null()));
    }

    #[test]
    fn disjoint_attrset_vs_list() {
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let list_ref = arc_ty!(&mut a, [Int]);
        let attrset = a[attrset_ref].clone();
        let list = a[list_ref].clone();
        assert!(are_output_types_disjoint(&attrset, &list));
        assert!(are_output_types_disjoint(&list, &attrset));
    }

    #[test]
    fn disjoint_attrset_vs_lambda() {
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let lambda = OutputTy::Lambda {
            param: arc_ty!(&mut a, Int),
            body: arc_ty!(&mut a, String),
        };
        assert!(are_output_types_disjoint(&attrset, &lambda));
        assert!(are_output_types_disjoint(&lambda, &attrset));
    }

    #[test]
    fn disjoint_list_vs_lambda() {
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        let lambda = OutputTy::Lambda {
            param: arc_ty!(&mut a, Int),
            body: arc_ty!(&mut a, String),
        };
        assert!(are_output_types_disjoint(&list, &lambda));
        assert!(are_output_types_disjoint(&lambda, &list));
    }

    #[test]
    fn disjoint_closed_attrsets_different_required_fields() {
        // Closed {x: Int} vs closed {y: String} — disjoint because
        // each requires a field the other doesn't have.
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "y": String });
        let attrset1 = a[r1].clone();
        let attrset2 = a[r2].clone();
        assert!(are_output_types_disjoint(&attrset1, &attrset2));
    }

    #[test]
    fn not_disjoint_closed_attrsets_shared_field() {
        // Closed {x: Int} vs closed {x: String} — NOT disjoint because
        // both have field `x` (they overlap structurally, the field types
        // could unify or not, but the attrset shapes aren't disjoint).
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "x": String });
        let attrset1 = a[r1].clone();
        let attrset2 = a[r2].clone();
        assert!(!are_output_types_disjoint(&attrset1, &attrset2));
    }

    #[test]
    fn disjoint_open_attrset_vs_closed_missing_required() {
        // Open {x: Int, ...} vs closed {y: String} — disjoint because
        // the open attrset requires `x` but the closed one doesn't have it.
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int; ... });
        let r2 = arc_ty!(&mut a, { "y": String });
        let open = a[r1].clone();
        let closed = a[r2].clone();
        assert!(are_output_types_disjoint(&open, &closed));
    }

    #[test]
    fn not_disjoint_open_attrsets() {
        // Open {x: Int, ...} vs open {y: String, ...} — NOT disjoint because
        // both are open, so a value with both fields could satisfy both.
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int; ... });
        let r2 = arc_ty!(&mut a, { "y": String; ... });
        let open1 = a[r1].clone();
        let open2 = a[r2].clone();
        assert!(!are_output_types_disjoint(&open1, &open2));
    }

    #[test]
    fn disjoint_closed_vs_open_attrset_missing_required_field() {
        // Closed {x: Int} vs open {y: String, ...} — disjoint because
        // the closed attrset doesn't have `y` which is required by the open one.
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "y": String; ... });
        let closed = a[r1].clone();
        let open = a[r2].clone();
        assert!(are_output_types_disjoint(&closed, &open));
    }

    #[test]
    fn not_disjoint_same_compound() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, [Int]);
        let r2 = arc_ty!(&mut a, [String]);
        let list1 = a[r1].clone();
        let list2 = a[r2].clone();
        assert!(!are_output_types_disjoint(&list1, &list2));
    }

    #[test]
    fn not_disjoint_tyvar() {
        // TyVar could be anything — can't prove disjointness.
        assert!(!are_output_types_disjoint(&OutputTy::TyVar(0), &int()));
        assert!(!are_output_types_disjoint(&int(), &OutputTy::TyVar(0)));
    }

    // -- has_type_contradiction cross-type tests ------------------------------

    #[test]
    fn contradiction_attrset_neg_attrset() {
        // {x: int} ∧ ¬{x: int} → contradiction (same attrset).
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let members = vec![attrset.clone(), neg(&mut a, attrset)];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn contradiction_list_neg_list() {
        // [int] ∧ ¬[int] → contradiction.
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        let members = vec![list.clone(), neg(&mut a, list)];
        assert!(has_type_contradiction(&a, &members));
    }

    #[test]
    fn no_contradiction_attrset_neg_null() {
        // {x: int} ∧ ¬null — not contradictory (different constructors).
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let members = vec![attrset, neg(&mut a, null())];
        assert!(!has_type_contradiction(&a, &members));
    }

    #[test]
    fn no_contradiction_list_neg_string() {
        // [int] ∧ ¬string — not contradictory.
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        let members = vec![list, neg(&mut a, string())];
        assert!(!has_type_contradiction(&a, &members));
    }

    // -- remove_redundant_negations tests ------------------------------------

    #[test]
    fn redundant_neg_removed_attrset_neg_null() {
        // {x: int} ∧ ¬null → {x: int} (attrset is inherently non-null).
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let members = vec![attrset.clone(), neg(&mut a, null())];
        let result = remove_redundant_negations(&a, members);
        assert_eq!(result, vec![attrset]);
    }

    #[test]
    fn redundant_neg_removed_list_neg_string() {
        // [int] ∧ ¬string → [int] (list is inherently non-string).
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        let members = vec![list.clone(), neg(&mut a, string())];
        let result = remove_redundant_negations(&a, members);
        assert_eq!(result, vec![list]);
    }

    #[test]
    fn redundant_neg_removed_number_neg_null() {
        // number ∧ ¬null → number (number and null are disjoint).
        let mut a = TypeArena::new();
        let members = vec![number(), neg(&mut a, null())];
        let result = remove_redundant_negations(&a, members);
        assert_eq!(result, vec![number()]);
    }

    #[test]
    fn redundant_neg_kept_when_only_tyvar() {
        // a ∧ ¬null — TyVar could be null, so ¬null is not redundant.
        let mut a = TypeArena::new();
        let members = vec![OutputTy::TyVar(0), neg(&mut a, null())];
        let result = remove_redundant_negations(&a, members.clone());
        assert_eq!(result, members);
    }

    #[test]
    fn redundant_neg_not_removed_when_overlapping() {
        // int ∧ ¬number — not redundant (Int <: Number, this is a contradiction,
        // but the negation itself is NOT redundant — it carries information).
        let mut a = TypeArena::new();
        let members = vec![int(), neg(&mut a, number())];
        let result = remove_redundant_negations(&a, members.clone());
        assert_eq!(result, members);
    }

    // -- tautology detection for compound types -------------------------------

    #[test]
    fn tautology_attrset_neg_attrset() {
        // {x: int} ∨ ¬{x: int} → empty (tautology).
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let members = vec![attrset.clone(), neg(&mut a, attrset)];
        let result = remove_tautological_pairs(&a, members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_list_neg_list() {
        // [int] ∨ ¬[int] → empty.
        let mut a = TypeArena::new();
        let list_ref = arc_ty!(&mut a, [Int]);
        let list = a[list_ref].clone();
        let members = vec![list.clone(), neg(&mut a, list)];
        let result = remove_tautological_pairs(&a, members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_compound_preserves_others() {
        // {x: int} ∨ ¬{x: int} ∨ string → string.
        let mut a = TypeArena::new();
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        let members = vec![attrset.clone(), neg(&mut a, attrset), string()];
        let result = remove_tautological_pairs(&a, members);
        assert_eq!(result, vec![string()]);
    }

    // -- is_output_subtype_or_equal tests --------------------------------------

    #[test]
    fn subtype_int_number() {
        assert!(is_output_subtype_or_equal(&int(), &number()));
    }

    #[test]
    fn subtype_float_number() {
        assert!(is_output_subtype_or_equal(&float(), &number()));
    }

    #[test]
    fn subtype_reflexive() {
        assert!(is_output_subtype_or_equal(&int(), &int()));
        assert!(is_output_subtype_or_equal(&string(), &string()));
    }

    #[test]
    fn not_subtype_number_int() {
        // Number is NOT a subtype of Int — Number also includes Float.
        assert!(!is_output_subtype_or_equal(&number(), &int()));
    }

    #[test]
    fn not_subtype_different_constructors() {
        let mut a = TypeArena::new();
        assert!(!is_output_subtype_or_equal(&int(), &string()));
        let attrset_ref = arc_ty!(&mut a, { "x": Int });
        let attrset = a[attrset_ref].clone();
        assert!(!is_output_subtype_or_equal(&int(), &attrset));
    }

    #[test]
    fn subtype_structural_equality_attrset() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "x": Int });
        let a1 = a[r1].clone();
        let a2 = a[r2].clone();
        assert!(is_output_subtype_or_equal(&a1, &a2));
    }

    // -- Regression: Number ∧ ¬Int is NOT a contradiction ----------------------

    #[test]
    fn no_contradiction_number_neg_int() {
        let mut a = TypeArena::new();
        let members = vec![number(), neg(&mut a, int())];
        assert!(
            !has_type_contradiction(&a, &members),
            "Number ∧ ¬Int should NOT be a contradiction (Number ⊄ Int)"
        );
    }

    #[test]
    fn no_contradiction_number_neg_float() {
        let mut a = TypeArena::new();
        let members = vec![number(), neg(&mut a, float())];
        assert!(
            !has_type_contradiction(&a, &members),
            "Number ∧ ¬Float should NOT be a contradiction (Number ⊄ Float)"
        );
    }

    // -- OutputTy::Top tests -------------------------------------------------

    #[test]
    fn tautology_produces_top_in_positive_canonicalization() {
        use crate::storage::TypeStorage;
        use lang_ty::Ty;

        let mut table = TypeStorage::new();
        let var_id = table.new_var();
        let int_ty = table.new_concrete(Ty::Primitive(PrimitiveTy::Int));
        let neg_int = table.new_concrete(Ty::Neg(int_ty));

        table.add_lower_bound(var_id, int_ty);
        table.add_lower_bound(var_id, neg_int);

        let (result_arena, result_ty) = canonicalize_standalone(&table, var_id, Positive);
        assert_eq!(
            result_arena[result_ty],
            OutputTy::Top,
            "int | ~int tautology should produce Top (any), got: {:?}",
            result_arena[result_ty]
        );
    }

    #[test]
    fn top_displays_as_any() {
        let mut a = TypeArena::new();
        let top = arc_ty!(&mut a, Top);
        assert_eq!(format!("{}", a.display(top)), "any");
    }

    #[test]
    fn top_identity_for_has_type_contradiction() {
        // Top in a contradiction check should be ignored (like TyVar).
        let mut a = TypeArena::new();
        let members = vec![OutputTy::Top, int(), neg(&mut a, string())];
        assert!(!has_type_contradiction(&a, &members));
    }

    // -- absorb_subsumed_union_members tests ----------------------------------

    #[test]
    fn absorb_open_wildcard_absorbs_open_with_fields() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { ; ... });
        let r2 = arc_ty!(&mut a, { "setenv": String; ... });
        let bare_open = a[r1].clone();
        let specific_open = a[r2].clone();
        let members = vec![bare_open.clone(), specific_open];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![bare_open]);
    }

    #[test]
    fn absorb_closed_not_absorbed() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "x": Int, "y": String });
        let aa = a[r1].clone();
        let bb = a[r2].clone();
        let members = vec![aa.clone(), bb.clone()];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![aa, bb]);
    }

    #[test]
    fn absorb_partial_subsumption_keeps_both() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int; ... });
        let r2 = arc_ty!(&mut a, { "y": String; ... });
        let aa = a[r1].clone();
        let bb = a[r2].clone();
        let members = vec![aa.clone(), bb.clone()];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![aa, bb]);
    }

    #[test]
    fn absorb_open_with_shared_fields() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int; ... });
        let r2 = arc_ty!(&mut a, { "x": Int, "y": String; ... });
        let general = a[r1].clone();
        let specific = a[r2].clone();
        let members = vec![general.clone(), specific];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![general]);
    }

    #[test]
    fn absorb_preserves_non_attrset_members() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { ; ... });
        let r2 = arc_ty!(&mut a, { "x": Int; ... });
        let bare_open = a[r1].clone();
        let specific = a[r2].clone();
        let members = vec![string(), bare_open.clone(), specific];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![string(), bare_open]);
    }

    // -- factor_shared_from_intersection tests --------------------------------

    #[test]
    fn factor_shared_basic() {
        // (int|string) & (bool|string) → string | (int & bool)
        let mut a = TypeArena::new();
        let members = vec![
            union(&mut a, vec![int(), string()]),
            union(&mut a, vec![bool_(), string()]),
        ];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                assert_eq!(parts.len(), 2, "union should have 2 members: {parts:?}");
                let has_string = parts.iter().any(|&p| a[p] == string());
                assert!(has_string, "should contain string");
                let has_intersection = parts
                    .iter()
                    .any(|&p| matches!(&a[p], OutputTy::Intersection(inner) if inner.len() == 2));
                assert!(
                    has_intersection,
                    "should contain intersection of remainders"
                );
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }

    #[test]
    fn factor_no_shared_unchanged() {
        let mut a = TypeArena::new();
        let u1 = union(&mut a, vec![int(), string()]);
        let u2 = union(&mut a, vec![bool_(), float()]);
        let members = vec![u1.clone(), u2.clone()];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result, vec![u1, u2]);
    }

    #[test]
    fn factor_fewer_than_two_unions_unchanged() {
        let mut a = TypeArena::new();
        let u1 = union(&mut a, vec![int(), string()]);
        let non_union = bool_();
        let members = vec![u1.clone(), non_union.clone()];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result, vec![non_union, u1]);
    }

    #[test]
    fn factor_mixed_union_and_non_union() {
        // (int|string) & (bool|string) & null → string | ((int & bool) & null)
        let mut a = TypeArena::new();
        let members = vec![
            union(&mut a, vec![int(), string()]),
            union(&mut a, vec![bool_(), string()]),
            null(),
        ];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                assert_eq!(parts.len(), 2, "should have shared + remainder: {parts:?}");
                let has_string = parts.iter().any(|&p| a[p] == string());
                assert!(has_string, "should contain shared string");
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }

    // -- merge_attrset_intersection tests ------------------------------------

    #[test]
    fn merge_inter_non_overlapping_fields() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "y": String });
        let m1 = a[r1].clone();
        let m2 = a[r2].clone();
        let result = merge_attrset_intersection(&mut a, vec![m1, m2]);
        assert_eq!(result.len(), 1, "should merge into one attrset: {result:?}");
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert_eq!(attr.fields.len(), 2);
                assert_eq!(a[attr.fields["x"]], int());
                assert_eq!(a[attr.fields["y"]], string());
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_overlapping_same_type() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "x": Int });
        let m1 = a[r1].clone();
        let m2 = a[r2].clone();
        let result = merge_attrset_intersection(&mut a, vec![m1, m2]);
        assert_eq!(result.len(), 1);
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert_eq!(a[attr.fields["x"]], int());
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_overlapping_different_type() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int });
        let r2 = arc_ty!(&mut a, { "x": String });
        let m1 = a[r1].clone();
        let m2 = a[r2].clone();
        let result = merge_attrset_intersection(&mut a, vec![m1, m2]);
        assert_eq!(result.len(), 1);
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert!(
                    matches!(&a[attr.fields["x"]], OutputTy::Intersection(parts) if parts.len() == 2),
                    "x should be Intersection, got: {:?}",
                    a[attr.fields["x"]]
                );
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_tyvar_replaced_by_concrete() {
        let mut a = TypeArena::new();
        let tyvar_ref = a.intern(OutputTy::TyVar(0));
        let m1 = OutputTy::AttrSet(AttrSetTy::from_internal([("x", tyvar_ref)], false));
        let r2 = arc_ty!(&mut a, { "x": Int });
        let m2 = a[r2].clone();
        let result = merge_attrset_intersection(&mut a, vec![m1, m2]);
        assert_eq!(result.len(), 1);
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert_eq!(a[attr.fields["x"]], int());
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_dyn_ty_intersection() {
        use lang_ty::AttrSetTy;
        let mut a = TypeArena::new();
        let int_ref = arc_ty!(&mut a, Int);
        let str_ref = arc_ty!(&mut a, String);
        let mut aa = AttrSetTy::<TyRef>::new();
        aa.dyn_ty = Some(int_ref);
        let mut bb = AttrSetTy::<TyRef>::new();
        bb.dyn_ty = Some(str_ref);
        let members = vec![OutputTy::AttrSet(aa), OutputTy::AttrSet(bb)];
        let result = merge_attrset_intersection(&mut a, members);
        assert_eq!(result.len(), 1);
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert!(attr.dyn_ty.is_some(), "should have dyn_ty");
                assert!(
                    matches!(&a[attr.dyn_ty.unwrap()], OutputTy::Intersection(parts) if parts.len() == 2),
                    "dyn_ty should be Intersection, got: {:?}",
                    a[attr.dyn_ty.unwrap()]
                );
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_open_all_open() {
        let mut a = TypeArena::new();
        let r1 = arc_ty!(&mut a, { "x": Int; ... });
        let r2 = arc_ty!(&mut a, { "y": String; ... });
        let open1 = a[r1].clone();
        let open2 = a[r2].clone();
        let result_both_open = merge_attrset_intersection(&mut a, vec![open1, open2]);
        assert_eq!(result_both_open.len(), 1);
        match &result_both_open[0] {
            OutputTy::AttrSet(attr) => assert!(attr.open, "both open → result open"),
            other => panic!("expected AttrSet, got: {other:?}"),
        }

        let r3 = arc_ty!(&mut a, { "x": Int; ... });
        let r4 = arc_ty!(&mut a, { "y": String });
        let open = a[r3].clone();
        let closed = a[r4].clone();
        let result_mixed = merge_attrset_intersection(&mut a, vec![open, closed]);
        assert_eq!(result_mixed.len(), 1);
        match &result_mixed[0] {
            OutputTy::AttrSet(attr) => assert!(!attr.open, "one closed → result closed"),
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn merge_inter_optional_all_agree() {
        use lang_ty::AttrSetTy;
        use std::collections::BTreeSet;
        let mut ar = TypeArena::new();
        let int_ref = arc_ty!(&mut ar, Int);
        let mut a = AttrSetTy::<TyRef>::from_internal([("x", int_ref)], false);
        a.optional_fields = BTreeSet::from([smol_str::SmolStr::from("x")]);
        let mut b = AttrSetTy::<TyRef>::from_internal([("x", int_ref)], false);
        b.optional_fields = BTreeSet::from([smol_str::SmolStr::from("x")]);
        let result =
            merge_attrset_intersection(&mut ar, vec![OutputTy::AttrSet(a), OutputTy::AttrSet(b)]);
        match &result[0] {
            OutputTy::AttrSet(attr) => {
                assert!(
                    attr.optional_fields.contains("x"),
                    "x optional in all → optional in result"
                );
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }

        // x optional in one, required in other → required.
        let mut c = AttrSetTy::<TyRef>::from_internal([("x", int_ref)], false);
        c.optional_fields = BTreeSet::from([smol_str::SmolStr::from("x")]);
        let d = AttrSetTy::<TyRef>::from_internal([("x", int_ref)], false);
        let result2 =
            merge_attrset_intersection(&mut ar, vec![OutputTy::AttrSet(c), OutputTy::AttrSet(d)]);
        match &result2[0] {
            OutputTy::AttrSet(attr) => {
                assert!(
                    !attr.optional_fields.contains("x"),
                    "x required in one → required in result"
                );
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    // -- flatten_composite tests (via flatten_union) --------------------------

    #[test]
    fn flatten_union_nested() {
        // Union([a, Union([b, c])]) → [a, b, c]
        let mut a = TypeArena::new();
        let inner = union(&mut a, vec![bool_(), float()]);
        let members = vec![int(), inner];
        let result = flatten_union(&a, members);
        assert_eq!(result.len(), 3);
        assert!(result.contains(&int()));
        assert!(result.contains(&bool_()));
        assert!(result.contains(&float()));
    }

    #[test]
    fn flatten_union_dedup() {
        // [a, b, a] → [a, b]
        let a = TypeArena::new();
        let members = vec![int(), string(), int()];
        let result = flatten_union(&a, members);
        assert_eq!(result.len(), 2, "duplicates should be removed: {result:?}");
        assert_eq!(result[0], int());
        assert_eq!(result[1], string());
    }

    #[test]
    fn flatten_large_n_no_nesting_skips_dedup() {
        // >64 members, no nesting → returns input unchanged (fast path).
        let a = TypeArena::new();
        let members: Vec<OutputTy> = (0..70).map(|i| OutputTy::TyVar(i)).collect();
        let result = flatten_union(&a, members.clone());
        assert_eq!(result.len(), 70, "fast path should return all members");
        assert_eq!(result, members);
    }

    // -- factor_shared_from_intersection additional tests ---------------------

    #[test]
    fn factor_three_unions_partial_shared() {
        let mut a = TypeArena::new();
        let members = vec![
            union(&mut a, vec![int(), string()]),
            union(&mut a, vec![string(), float()]),
            union(&mut a, vec![int(), string()]),
        ];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                let has_string = parts.iter().any(|&p| a[p] == string());
                assert!(has_string, "string should be in shared set");
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }

    #[test]
    fn factor_all_members_shared() {
        let mut a = TypeArena::new();
        let members = vec![
            union(&mut a, vec![int(), string()]),
            union(&mut a, vec![int(), string()]),
        ];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                assert_eq!(parts.len(), 2, "should have both shared members");
                let types: Vec<_> = parts.iter().map(|&p| a[p].clone()).collect();
                assert!(types.contains(&int()));
                assert!(types.contains(&string()));
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }

    #[test]
    fn factor_single_element_remainders() {
        let mut a = TypeArena::new();
        let members = vec![
            union(&mut a, vec![int(), bool_()]),
            union(&mut a, vec![bool_(), float()]),
        ];
        let result = factor_shared_from_intersection(&mut a, members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                let has_bool = parts.iter().any(|&p| a[p] == bool_());
                assert!(has_bool, "shared bool should be present");
                let has_isect = parts
                    .iter()
                    .any(|&p| matches!(&a[p], OutputTy::Intersection(inner) if inner.len() == 2));
                assert!(has_isect, "remainders should be intersected: {parts:?}");
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }
}
