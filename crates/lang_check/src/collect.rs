// ==============================================================================
// Polarity-Aware Canonicalization
// ==============================================================================
//
// Converts internal TyId representation to canonical OutputTy.
// Variables are expanded based on polarity:
// - Positive position (output): variable → union of lower bounds
// - Negative position (input): variable → intersection of upper bounds
// Lambda params flip polarity.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Instant;

use la_arena::ArenaMap;

use smol_str::SmolStr;

use super::{CheckCtx, InferenceResult, Polarity, TyId};
use crate::storage::{TypeEntry, TypeStorage};
use lang_ty::{
    disjoint::{are_shapes_disjoint, ConstructorShape},
    AttrSetTy, OutputTy, Ty, TyRef,
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
    alias_provenance: &'a HashMap<TyId, SmolStr>,
    cache: HashMap<(TyId, Polarity), OutputTy>,
    in_progress: HashSet<(TyId, Polarity)>,
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
    fn new(table: &'a TypeStorage, alias_provenance: &'a HashMap<TyId, SmolStr>) -> Self {
        Self {
            table,
            alias_provenance,
            cache: HashMap::new(),
            in_progress: HashSet::new(),
            deadline: None,
            op_counter: 0,
            deadline_exceeded: false,
        }
    }

    fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    fn canonicalize(&mut self, ty_id: TyId, polarity: Polarity) -> OutputTy {
        // Fast path: if deadline already exceeded, return degraded type.
        if self.deadline_exceeded {
            return OutputTy::TyVar(ty_id.0);
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
                return OutputTy::TyVar(ty_id.0);
            }
        }

        let key = (ty_id, polarity);

        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }

        if self.in_progress.contains(&key) {
            return OutputTy::TyVar(ty_id.0);
        }

        // Guard against stack overflow on deeply nested type graphs.
        // canonicalize is the single recursive entry point — expand_bounds,
        // canonicalize_inner, and canonicalize_concrete all recurse through here.
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            self.in_progress.insert(key);
            let result = self.canonicalize_inner(ty_id, polarity);
            self.in_progress.remove(&key);

            self.cache.insert(key, result.clone());
            result
        })
    }

    fn canonicalize_inner(&mut self, ty_id: TyId, polarity: Polarity) -> OutputTy {
        let alias_name = self.alias_provenance.get(&ty_id).cloned();

        // Clone only the data we need: for variables, just the relevant bounds
        // Vec (Vec<TyId> ~ Vec<u32>, cheap); for concrete types, the Ty value.
        // This avoids cloning the unused bounds Vec for variables.
        let result = if let Some(v) = self.table.get_var(ty_id) {
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
        };

        // If this TyId originated from a type alias, wrap the canonical form
        // in Named so display shows the alias name instead of the expansion.
        if let Some(name) = alias_name {
            OutputTy::Named(name, TyRef::from(result))
        } else {
            result
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
        // Copy TyIds into a local Vec to release the borrow on `bounds`
        // before calling `self.canonicalize()` which needs `&mut self`.
        let bounds = bounds.to_vec();

        // 1. Canonicalize each bound at the given polarity.
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, polarity))
            .collect();

        // 2. Flatten nested composites.
        let flattened = match polarity {
            Positive => flatten_union(members),
            Negative => flatten_intersection(members),
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
                let concrete = remove_tautological_pairs(concrete);
                // Absorb open attrsets subsumed by more general open attrsets.
                absorb_subsumed_union_members(concrete)
            }
            Negative => {
                // Merge multiple attrsets into one (intersection of records =
                // record with all fields).
                let concrete = merge_attrset_intersection(concrete);
                // Remove redundant negations: when an intersection contains a
                // concrete type T and Neg(S) where T and S are provably disjoint,
                // the negation adds no information. E.g. `{name: string} & ~null`
                // simplifies to `{name: string}` because attrsets are inherently
                // non-null. Only removes when the positive member has a known
                // constructor (not a TyVar).
                let concrete = remove_redundant_negations(concrete);
                // Contradiction detection: T ∧ ¬S = ⊥ when T ⊆ S.
                if has_type_contradiction(&concrete) {
                    return OutputTy::Bottom;
                }
                // Factor shared members from intersections of unions:
                // (A|C) & (B|C) = C | (A&B).
                factor_shared_from_intersection(concrete)
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
                Positive => OutputTy::Union(concrete.into_iter().map(TyRef::from).collect()),
                Negative => OutputTy::Intersection(concrete.into_iter().map(TyRef::from).collect()),
            },
        }
    }

    /// Fallback when a variable has no concrete bounds in the given polarity.
    ///
    /// - **Positive**: check for atom-only upper bounds (primitives, negations of
    ///   primitives) as a display heuristic. `ret <: Number` becomes `number`
    ///   rather than a bare type variable. If no atom uppers, return TyVar.
    /// - **Negative**: return a bare TyVar.
    fn expand_bounds_empty_fallback(&mut self, var_id: TyId, polarity: Polarity) -> OutputTy {
        if polarity == Negative {
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
            Ty::List(elem) => {
                let c_elem = self.canonicalize(*elem, polarity);
                OutputTy::List(TyRef::from(c_elem))
            }
            Ty::Lambda { param, body } => {
                let c_param = self.canonicalize(*param, polarity.flip());
                let c_body = self.canonicalize(*body, polarity);
                OutputTy::Lambda {
                    param: TyRef::from(c_param),
                    body: TyRef::from(c_body),
                }
            }
            Ty::AttrSet(attr) => {
                let mut new_fields = BTreeMap::new();
                for (k, &v) in &attr.fields {
                    let c_field = self.canonicalize(v, polarity);
                    new_fields.insert(k.clone(), TyRef::from(c_field));
                }
                let dyn_ty = attr
                    .dyn_ty
                    .map(|d| TyRef::from(self.canonicalize(d, polarity)));
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
                negate_output_ty(c_inner)
            }

            // Intersection: canonicalize both members and flatten/normalize
            // using the same logic as variable bound expansion.
            Ty::Inter(a, b) => {
                let ca = self.canonicalize(*a, polarity);
                let cb = self.canonicalize(*b, polarity);
                let members = flatten_intersection(vec![ca, cb]);
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
                if has_type_contradiction(&concrete) {
                    return OutputTy::Bottom;
                }
                let had_concrete = !concrete.is_empty();
                let concrete = match polarity {
                    Positive => {
                        let c = remove_redundant_negations(concrete);
                        remove_tautological_pairs(c)
                    }
                    Negative => {
                        let c = merge_attrset_intersection(concrete);
                        remove_redundant_negations(c)
                    }
                };
                // Factor shared members from intersections of unions:
                // (A|C) & (B|C) = C | (A&B).
                let concrete = factor_shared_from_intersection(concrete);
                match concrete.len() {
                    // Tautology removal emptied a non-empty vec in positive
                    // position — return Top.
                    0 if had_concrete && polarity == Positive => OutputTy::Top,
                    // All concrete members were filtered out. Fall back to
                    // the first member before filtering (a TyVar or Bottom).
                    0 => all_members.into_iter().next().unwrap_or(OutputTy::Bottom),
                    1 => concrete.into_iter().next().unwrap(),
                    _ => OutputTy::Intersection(concrete.into_iter().map(TyRef::from).collect()),
                }
            }

            // Union: canonicalize both members and flatten/normalize.
            Ty::Union(a, b) => {
                let ca = self.canonicalize(*a, polarity);
                let cb = self.canonicalize(*b, polarity);
                let members = flatten_union(vec![ca, cb]);
                let all_members = members.clone();
                let concrete: Vec<OutputTy> = members
                    .into_iter()
                    .filter(|m| !matches!(m, OutputTy::TyVar(_) | OutputTy::Bottom | OutputTy::Top))
                    .collect();
                let had_concrete = !concrete.is_empty();
                let concrete = match polarity {
                    Positive => {
                        let c = remove_tautological_pairs(concrete);
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
                    _ => OutputTy::Union(concrete.into_iter().map(TyRef::from).collect()),
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
    alias_provenance: &HashMap<TyId, SmolStr>,
    ty_id: TyId,
    polarity: Polarity,
) -> OutputTy {
    canonicalize_standalone_with_deadline(table, alias_provenance, ty_id, polarity, None)
}

pub fn canonicalize_standalone_with_deadline(
    table: &TypeStorage,
    alias_provenance: &HashMap<TyId, SmolStr>,
    ty_id: TyId,
    polarity: Polarity,
    deadline: Option<Instant>,
) -> OutputTy {
    let mut canon = Canonicalizer::new(table, alias_provenance);
    if let Some(d) = deadline {
        canon = canon.with_deadline(d);
    }
    canon.canonicalize(ty_id, polarity)
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
fn negate_output_ty(inner: OutputTy) -> OutputTy {
    // Guard against stack overflow on deeply nested Union/Intersection trees
    // (De Morgan expansion recurses independently of canonicalize).
    stacker::maybe_grow(256 * 1024, 1024 * 1024, || match inner {
        // ¬(¬A) → A
        OutputTy::Neg(a) => (*a.0).clone(),

        // ¬(A ∨ B ∨ …) → ¬A ∧ ¬B ∧ …
        OutputTy::Union(members) => OutputTy::Intersection(
            members
                .into_iter()
                .map(|m| TyRef::from(negate_output_ty((*m.0).clone())))
                .collect(),
        ),

        // ¬(A ∧ B ∧ …) → ¬A ∨ ¬B ∨ …
        OutputTy::Intersection(members) => OutputTy::Union(
            members
                .into_iter()
                .map(|m| TyRef::from(negate_output_ty((*m.0).clone())))
                .collect(),
        ),

        // Leaf or compound type that isn't union/intersection/neg — just wrap.
        other => OutputTy::Neg(TyRef::from(other)),
    })
}

/// Remove tautological pairs from a union: `T ∨ ¬T` = ⊤.
/// When both a type and its negation appear, both are dropped since their
/// union is the top type and adds no information to the overall union.
///
/// Handles all constructor kinds — primitives, attrsets, lists, lambdas — by
/// checking structural equality between positive members and negated members.
/// For primitives, also handles subtype tautologies (Int ∨ ¬Int).
fn remove_tautological_pairs(members: Vec<OutputTy>) -> Vec<OutputTy> {
    // Collect negated inner types.
    let negated_inners: Vec<&OutputTy> = members
        .iter()
        .filter_map(|m| match m {
            OutputTy::Neg(inner) => Some(&*inner.0),
            _ => None,
        })
        .collect();

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
    let mut tautological_positives: HashSet<usize> = HashSet::new();
    let mut tautological_negatives: HashSet<usize> = HashSet::new();

    for (pi, pos) in positives.iter().enumerate() {
        for (ni, neg_inner) in negated_inners.iter().enumerate() {
            if pos == neg_inner {
                tautological_positives.insert(pi);
                tautological_negatives.insert(ni);
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
    let attrset_indices: Vec<usize> = members
        .iter()
        .enumerate()
        .filter_map(|(i, m)| matches!(m, OutputTy::AttrSet(_)).then_some(i))
        .collect();

    if attrset_indices.len() < 2 {
        return members;
    }

    // Mark indices that are subsumed by another attrset in the union.
    let mut subsumed: HashSet<usize> = HashSet::new();
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
                subsumed.insert(j);
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
fn factor_shared_from_intersection(members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut unions: Vec<Vec<OutputTy>> = Vec::new();
    let mut non_unions: Vec<OutputTy> = Vec::new();

    for m in members {
        match m {
            OutputTy::Union(inner) => {
                unions.push(inner.into_iter().map(|r| (*r.0).clone()).collect());
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
                _ => result.push(OutputTy::Union(u.into_iter().map(TyRef::from).collect())),
            }
        }
        return result;
    }

    // Find members present in ALL unions. Use the first union as the candidate
    // set and intersect with each subsequent union.
    let mut shared: HashSet<OutputTy> = unions[0].iter().cloned().collect();
    for u in &unions[1..] {
        let u_set: HashSet<OutputTy> = u.iter().cloned().collect();
        shared.retain(|m| u_set.contains(m));
    }

    if shared.is_empty() {
        // No shared members — reassemble unchanged.
        let mut result = non_unions;
        for u in unions {
            result.push(OutputTy::Union(u.into_iter().map(TyRef::from).collect()));
        }
        return result;
    }

    // Remove shared members from each union, producing remainders.
    let remainders: Vec<OutputTy> = unions
        .into_iter()
        .filter_map(|u| {
            let remainder: Vec<OutputTy> = u.into_iter().filter(|m| !shared.contains(m)).collect();
            match remainder.len() {
                0 => None,
                1 => Some(remainder.into_iter().next().unwrap()),
                _ => Some(OutputTy::Union(
                    remainder.into_iter().map(TyRef::from).collect(),
                )),
            }
        })
        .collect();

    // Build the factored result: shared | (remainders & non_unions)
    let mut shared_vec: Vec<OutputTy> = shared.into_iter().collect();
    shared_vec.sort();

    // Build the intersection of remainders + non_unions.
    let mut intersection_parts: Vec<OutputTy> = remainders;
    intersection_parts.extend(non_unions);

    if intersection_parts.is_empty() {
        // All union members were shared — result is just the shared union.
        match shared_vec.len() {
            1 => vec![shared_vec.into_iter().next().unwrap()],
            _ => vec![OutputTy::Union(
                shared_vec.into_iter().map(TyRef::from).collect(),
            )],
        }
    } else {
        // Result is shared | intersection(remainders, non_unions).
        let intersection = match intersection_parts.len() {
            1 => intersection_parts.into_iter().next().unwrap(),
            _ => OutputTy::Intersection(intersection_parts.into_iter().map(TyRef::from).collect()),
        };
        shared_vec.push(intersection);
        // Return as a single-element vec containing the final Union.
        // The caller (expand_bounds/canonicalize_concrete) will wrap in
        // Intersection if there are multiple members, but we've already
        // restructured into a Union, so return it as one element.
        vec![OutputTy::Union(
            shared_vec.into_iter().map(TyRef::from).collect(),
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
fn has_type_contradiction(members: &[OutputTy]) -> bool {
    // Collect positive (non-negated) and negated inner types.
    let mut positives: Vec<&OutputTy> = Vec::new();
    let mut negated_inners: Vec<&OutputTy> = Vec::new();

    for m in members {
        match m {
            OutputTy::Neg(inner) => negated_inners.push(&inner.0),
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
    for i in 0..positives.len() {
        for j in (i + 1)..positives.len() {
            if are_output_types_disjoint(positives[i], positives[j]) {
                return true;
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
    // Build owned key maps for attrset shapes upfront so borrows outlive the
    // shape references.
    let a_keys: BTreeMap<SmolStr, ()>;
    let b_keys: BTreeMap<SmolStr, ()>;

    let a_shape = match a {
        OutputTy::Primitive(p) => ConstructorShape::Primitive(*p),
        OutputTy::AttrSet(attr) => {
            a_keys = attr.fields.keys().map(|k| (k.clone(), ())).collect();
            ConstructorShape::AttrSet {
                fields: &a_keys,
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
            b_keys = attr.fields.keys().map(|k| (k.clone(), ())).collect();
            ConstructorShape::AttrSet {
                fields: &b_keys,
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
fn remove_redundant_negations(members: Vec<OutputTy>) -> Vec<OutputTy> {
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
    let concrete_indices: Vec<usize> = members
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
    let keep: Vec<bool> = members
        .iter()
        .map(|m| {
            if let OutputTy::Neg(inner) = m {
                // Keep this negation only if it's NOT disjoint from all concrete
                // positives. If it IS disjoint from every positive, it's redundant.
                !concrete_indices
                    .iter()
                    .all(|&i| are_output_types_disjoint(&members[i], &inner.0))
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
    members: Vec<OutputTy>,
    extract_nested: fn(&OutputTy) -> Option<&Vec<TyRef>>,
) -> Vec<OutputTy> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for m in members {
        if let Some(inner) = extract_nested(&m) {
            for sub in inner {
                // Check containment first (by ref, no clone) to avoid cloning
                // items we've already seen.
                if !seen.contains(&*sub.0) {
                    let sub_ty = (*sub.0).clone();
                    seen.insert(sub_ty.clone());
                    result.push(sub_ty);
                }
            }
        } else if !seen.contains(&m) {
            seen.insert(m.clone());
            result.push(m);
        }
    }
    result
}

fn flatten_union(members: Vec<OutputTy>) -> Vec<OutputTy> {
    flatten_composite(members, |ty| match ty {
        OutputTy::Union(inner) => Some(inner),
        _ => None,
    })
}

fn flatten_intersection(members: Vec<OutputTy>) -> Vec<OutputTy> {
    flatten_composite(members, |ty| match ty {
        OutputTy::Intersection(inner) => Some(inner),
        _ => None,
    })
}

/// Merge multiple attrsets in an intersection into a single attrset.
/// The intersection of `{ foo: int }` and `{ bar: string }` is `{ foo: int, bar: string }`.
/// For overlapping fields, the field types are intersected.
fn merge_attrset_intersection(members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut attrsets: Vec<AttrSetTy<TyRef>> = Vec::new();
    let mut others: Vec<OutputTy> = Vec::new();

    for m in members {
        match m {
            OutputTy::AttrSet(attr) => attrsets.push(attr),
            other => others.push(other),
        }
    }

    if attrsets.is_empty() {
        return others;
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
                merged_dyn = Some(TyRef::from(OutputTy::Intersection(vec![
                    existing.clone(),
                    new.clone(),
                ])));
            }
            _ => {}
        }
        for (k, v) in &attr.fields {
            merged_fields
                .entry(k.clone())
                .and_modify(|existing| {
                    if matches!(&*existing.0, OutputTy::TyVar(_)) {
                        *existing = v.clone();
                    } else if *existing != *v {
                        *existing =
                            TyRef::from(OutputTy::Intersection(vec![existing.clone(), v.clone()]));
                    }
                })
                .or_insert_with(|| v.clone());
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
    others
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
        let mut canon = Canonicalizer::new(&self.ctx.types.storage, &self.ctx.alias_provenance);
        if let Some(d) = canon_deadline {
            canon = canon.with_deadline(d);
        }

        for (name, ty) in name_tys {
            // Prefer the early-canonicalized type (captured before use-site
            // extrusion contaminated the bounds) over late canonicalization.
            let output = if let Some(early) = self.ctx.early_canonical.get(name) {
                if matches!(early, OutputTy::TyVar(_)) {
                    // The early snapshot captured no type information (bare variable),
                    // likely because enclosing lambda parameter annotations hadn't
                    // propagated yet. Fall back to late canonicalization which sees
                    // the fully-constrained bounds — unless the deadline was exceeded,
                    // in which case use a degraded unconstrained type to avoid
                    // expensive canonicalization on degenerate type graphs.
                    if deadline_exceeded {
                        OutputTy::TyVar(0)
                    } else {
                        canon.canonicalize(ty, Positive)
                    }
                } else {
                    early.clone()
                }
            } else if deadline_exceeded {
                // When the deadline was exceeded, use a degraded unconstrained type
                // for names without an early-canonical snapshot. Late canonicalization
                // can be very expensive on degenerate type graphs from partial inference.
                OutputTy::TyVar(0)
            } else {
                canon.canonicalize(ty, Positive)
            };
            name_ty_map.insert(name, output.normalize_vars());
        }

        // When the inference deadline was exceeded, skip expression-level
        // canonicalization. It iterates over every expression in the module
        // and can be very expensive when the type graph has degenerate bounds
        // from partial inference. Name-level types (above) are sufficient for
        // hover/completion; expr-level types are mainly used for diagnostics
        // and inlay hints, which are less critical on timed-out files.
        if !deadline_exceeded {
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
                let mut output = canon.canonicalize(ty, Positive);
                if expr == self.ctx.module.entry_expr {
                    output = output.normalize_vars();
                }
                expr_ty_map.insert(expr, output);
            }
        }

        InferenceResult {
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
    use lang_ty::arc_ty;

    // -- negate_output_ty tests -----------------------------------------------

    #[test]
    fn negate_double_neg() {
        // ¬(¬Int) → Int
        let inner = OutputTy::Neg(TyRef::from(arc_ty!(Int)));
        let negated = negate_output_ty(inner);
        // Double negation in negate_output_ty: Neg(Neg(x)) matches the Neg arm,
        // but the input is Neg(Int) — the outer negate_output_ty sees Neg(Int)
        // and returns the inner Int.
        assert_eq!(negated, arc_ty!(Int));
    }

    #[test]
    fn negate_union_de_morgan() {
        // ¬(Int ∨ String) → ¬Int ∧ ¬String
        let input = arc_ty!(union!(Int, String));
        let result = negate_output_ty(input);
        let expected = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(Int)))),
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(String)))),
        ]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_intersection_de_morgan() {
        // ¬(Int ∧ String) → ¬Int ∨ ¬String
        let input = arc_ty!(isect!(Int, String));
        let result = negate_output_ty(input);
        let expected = OutputTy::Union(vec![
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(Int)))),
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(String)))),
        ]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_nested_de_morgan() {
        // ¬(¬Int ∨ String) → ¬(¬Int) ∧ ¬String → Int ∧ ¬String
        let input = OutputTy::Union(vec![
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(Int)))),
            TyRef::from(arc_ty!(String)),
        ]);
        let result = negate_output_ty(input);
        let expected = OutputTy::Intersection(vec![
            TyRef::from(arc_ty!(Int)),
            TyRef::from(OutputTy::Neg(TyRef::from(arc_ty!(String)))),
        ]);
        assert_eq!(result, expected);
    }

    #[test]
    fn negate_primitive_wraps() {
        // ¬Int → Neg(Int)
        let result = negate_output_ty(arc_ty!(Int));
        assert_eq!(result, OutputTy::Neg(TyRef::from(arc_ty!(Int))));
    }

    // -- has_type_contradiction tests -------------------------------------

    #[test]
    fn contradiction_exact_match() {
        // Int ∧ ¬Int → contradiction
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(Int)))];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn contradiction_subtype() {
        // Int ∧ ¬Number → contradiction (Int <: Number)
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(Number)))];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn contradiction_float_subtype() {
        // Float ∧ ¬Number → contradiction (Float <: Number)
        let members = vec![arc_ty!(Float), OutputTy::Neg(TyRef::from(arc_ty!(Number)))];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn no_contradiction_different_types() {
        // Int ∧ ¬String — no contradiction
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(String)))];
        assert!(!has_type_contradiction(&members));
    }

    #[test]
    fn contradiction_disjoint_positives() {
        // Int ∧ String — disjoint primitives, IS a contradiction.
        let members = vec![arc_ty!(Int), arc_ty!(String)];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn no_contradiction_same_positives() {
        // Int ∧ Int — same type, no contradiction.
        let members = vec![arc_ty!(Int), arc_ty!(Int)];
        assert!(!has_type_contradiction(&members));
    }

    // -- remove_tautological_pairs tests --------------------------------------

    #[test]
    fn tautology_exact_match() {
        // Int ∨ ¬Int → empty (both removed)
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(Int)))];
        let result = remove_tautological_pairs(members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_preserves_other_members() {
        // Int ∨ ¬Int ∨ String → String
        let members = vec![
            arc_ty!(Int),
            OutputTy::Neg(TyRef::from(arc_ty!(Int))),
            arc_ty!(String),
        ];
        let result = remove_tautological_pairs(members);
        assert_eq!(result, vec![arc_ty!(String)]);
    }

    #[test]
    fn no_tautology_different_types() {
        // Int ∨ ¬String — no tautology, kept as-is
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(String)))];
        let result = remove_tautological_pairs(members.clone());
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
        let int_ty = table.new_concrete(Ty::Primitive(lang_ty::PrimitiveTy::Int));
        let neg_int = table.new_concrete(Ty::Neg(int_ty));

        // Add int and ~int as upper bounds of the variable.
        table.add_upper_bound(var_id, int_ty);
        table.add_upper_bound(var_id, neg_int);

        let provenance = std::collections::HashMap::new();
        let result = canonicalize_standalone(&table, &provenance, var_id, Negative);
        assert_eq!(
            result,
            arc_ty!(Bottom),
            "int & ~int contradiction should produce Bottom (never), got: {result}"
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
        let string_ty = table.new_concrete(Ty::Primitive(lang_ty::PrimitiveTy::String));
        let null_ty = table.new_concrete(Ty::Primitive(lang_ty::PrimitiveTy::Null));
        let neg_null = table.new_concrete(Ty::Neg(null_ty));

        table.add_upper_bound(var_id, string_ty);
        table.add_upper_bound(var_id, neg_null);

        let provenance = std::collections::HashMap::new();
        let result = canonicalize_standalone(&table, &provenance, var_id, Negative);
        // ~null is redundant alongside string (disjoint constructors), so
        // it gets removed, leaving just string.
        assert_eq!(
            result,
            arc_ty!(String),
            "string & ~null should simplify to string, got: {result}"
        );
    }

    // -- are_output_types_disjoint tests --------------------------------------

    #[test]
    fn disjoint_primitive_vs_primitive() {
        assert!(are_output_types_disjoint(&arc_ty!(Int), &arc_ty!(String)));
        assert!(are_output_types_disjoint(&arc_ty!(Null), &arc_ty!(Bool)));
        assert!(are_output_types_disjoint(&arc_ty!(Path), &arc_ty!(Float)));
    }

    #[test]
    fn not_disjoint_same_primitive() {
        assert!(!are_output_types_disjoint(&arc_ty!(Int), &arc_ty!(Int)));
        assert!(!are_output_types_disjoint(
            &arc_ty!(String),
            &arc_ty!(String)
        ));
    }

    #[test]
    fn not_disjoint_subtype_primitives() {
        // Int and Number overlap (Int <: Number).
        assert!(!are_output_types_disjoint(&arc_ty!(Int), &arc_ty!(Number)));
        assert!(!are_output_types_disjoint(&arc_ty!(Number), &arc_ty!(Int)));
        // Float and Number overlap (Float <: Number).
        assert!(!are_output_types_disjoint(
            &arc_ty!(Float),
            &arc_ty!(Number)
        ));
    }

    #[test]
    fn disjoint_primitive_vs_attrset() {
        let attrset = arc_ty!({ "name": String });
        assert!(are_output_types_disjoint(&arc_ty!(Null), &attrset));
        assert!(are_output_types_disjoint(&attrset, &arc_ty!(Null)));
        assert!(are_output_types_disjoint(&arc_ty!(Int), &attrset));
    }

    #[test]
    fn disjoint_primitive_vs_list() {
        let list = arc_ty!([Int]);
        assert!(are_output_types_disjoint(&arc_ty!(String), &list));
        assert!(are_output_types_disjoint(&list, &arc_ty!(String)));
    }

    #[test]
    fn disjoint_primitive_vs_lambda() {
        let lambda = OutputTy::Lambda {
            param: TyRef::from(arc_ty!(Int)),
            body: TyRef::from(arc_ty!(String)),
        };
        assert!(are_output_types_disjoint(&arc_ty!(Null), &lambda));
        assert!(are_output_types_disjoint(&lambda, &arc_ty!(Null)));
    }

    #[test]
    fn disjoint_attrset_vs_list() {
        let attrset = arc_ty!({ "x": Int });
        let list = arc_ty!([Int]);
        assert!(are_output_types_disjoint(&attrset, &list));
        assert!(are_output_types_disjoint(&list, &attrset));
    }

    #[test]
    fn disjoint_attrset_vs_lambda() {
        let attrset = arc_ty!({ "x": Int });
        let lambda = OutputTy::Lambda {
            param: TyRef::from(arc_ty!(Int)),
            body: TyRef::from(arc_ty!(String)),
        };
        assert!(are_output_types_disjoint(&attrset, &lambda));
        assert!(are_output_types_disjoint(&lambda, &attrset));
    }

    #[test]
    fn disjoint_list_vs_lambda() {
        let list = arc_ty!([Int]);
        let lambda = OutputTy::Lambda {
            param: TyRef::from(arc_ty!(Int)),
            body: TyRef::from(arc_ty!(String)),
        };
        assert!(are_output_types_disjoint(&list, &lambda));
        assert!(are_output_types_disjoint(&lambda, &list));
    }

    #[test]
    fn disjoint_closed_attrsets_different_required_fields() {
        // Closed {x: Int} vs closed {y: String} — disjoint because
        // each requires a field the other doesn't have.
        let attrset1 = arc_ty!({ "x": Int });
        let attrset2 = arc_ty!({ "y": String });
        assert!(are_output_types_disjoint(&attrset1, &attrset2));
    }

    #[test]
    fn not_disjoint_closed_attrsets_shared_field() {
        // Closed {x: Int} vs closed {x: String} — NOT disjoint because
        // both have field `x` (they overlap structurally, the field types
        // could unify or not, but the attrset shapes aren't disjoint).
        let attrset1 = arc_ty!({ "x": Int });
        let attrset2 = arc_ty!({ "x": String });
        assert!(!are_output_types_disjoint(&attrset1, &attrset2));
    }

    #[test]
    fn disjoint_open_attrset_vs_closed_missing_required() {
        // Open {x: Int, ...} vs closed {y: String} — disjoint because
        // the open attrset requires `x` but the closed one doesn't have it.
        let open = arc_ty!({ "x": Int; ... });
        let closed = arc_ty!({ "y": String });
        assert!(are_output_types_disjoint(&open, &closed));
    }

    #[test]
    fn not_disjoint_open_attrsets() {
        // Open {x: Int, ...} vs open {y: String, ...} — NOT disjoint because
        // both are open, so a value with both fields could satisfy both.
        let open1 = arc_ty!({ "x": Int; ... });
        let open2 = arc_ty!({ "y": String; ... });
        assert!(!are_output_types_disjoint(&open1, &open2));
    }

    #[test]
    fn disjoint_closed_vs_open_attrset_missing_required_field() {
        // Closed {x: Int} vs open {y: String, ...} — disjoint because
        // the closed attrset doesn't have `y` which is required by the open one.
        let closed = arc_ty!({ "x": Int });
        let open = arc_ty!({ "y": String; ... });
        assert!(are_output_types_disjoint(&closed, &open));
    }

    #[test]
    fn not_disjoint_same_compound() {
        let list1 = arc_ty!([Int]);
        let list2 = arc_ty!([String]);
        assert!(!are_output_types_disjoint(&list1, &list2));
    }

    #[test]
    fn not_disjoint_tyvar() {
        // TyVar could be anything — can't prove disjointness.
        assert!(!are_output_types_disjoint(
            &OutputTy::TyVar(0),
            &arc_ty!(Int)
        ));
        assert!(!are_output_types_disjoint(
            &arc_ty!(Int),
            &OutputTy::TyVar(0)
        ));
    }

    // -- has_type_contradiction cross-type tests ------------------------------

    #[test]
    fn contradiction_attrset_neg_attrset() {
        // {x: int} ∧ ¬{x: int} → contradiction (same attrset).
        let attrset = arc_ty!({ "x": Int });
        let members = vec![attrset.clone(), OutputTy::Neg(TyRef::from(attrset))];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn contradiction_list_neg_list() {
        // [int] ∧ ¬[int] → contradiction.
        let list = arc_ty!([Int]);
        let members = vec![list.clone(), OutputTy::Neg(TyRef::from(list))];
        assert!(has_type_contradiction(&members));
    }

    #[test]
    fn no_contradiction_attrset_neg_null() {
        // {x: int} ∧ ¬null — not contradictory (different constructors).
        let members = vec![
            arc_ty!({ "x": Int }),
            OutputTy::Neg(TyRef::from(arc_ty!(Null))),
        ];
        assert!(!has_type_contradiction(&members));
    }

    #[test]
    fn no_contradiction_list_neg_string() {
        // [int] ∧ ¬string — not contradictory.
        let members = vec![arc_ty!([Int]), OutputTy::Neg(TyRef::from(arc_ty!(String)))];
        assert!(!has_type_contradiction(&members));
    }

    // -- remove_redundant_negations tests ------------------------------------

    #[test]
    fn redundant_neg_removed_attrset_neg_null() {
        // {x: int} ∧ ¬null → {x: int} (attrset is inherently non-null).
        let attrset = arc_ty!({ "x": Int });
        let members = vec![attrset.clone(), OutputTy::Neg(TyRef::from(arc_ty!(Null)))];
        let result = remove_redundant_negations(members);
        assert_eq!(result, vec![attrset]);
    }

    #[test]
    fn redundant_neg_removed_list_neg_string() {
        // [int] ∧ ¬string → [int] (list is inherently non-string).
        let list = arc_ty!([Int]);
        let members = vec![list.clone(), OutputTy::Neg(TyRef::from(arc_ty!(String)))];
        let result = remove_redundant_negations(members);
        assert_eq!(result, vec![list]);
    }

    #[test]
    fn redundant_neg_removed_number_neg_null() {
        // number ∧ ¬null → number (number and null are disjoint).
        let members = vec![arc_ty!(Number), OutputTy::Neg(TyRef::from(arc_ty!(Null)))];
        let result = remove_redundant_negations(members);
        assert_eq!(result, vec![arc_ty!(Number)]);
    }

    #[test]
    fn redundant_neg_kept_when_only_tyvar() {
        // a ∧ ¬null — TyVar could be null, so ¬null is not redundant.
        let members = vec![
            OutputTy::TyVar(0),
            OutputTy::Neg(TyRef::from(arc_ty!(Null))),
        ];
        let result = remove_redundant_negations(members.clone());
        assert_eq!(result, members);
    }

    #[test]
    fn redundant_neg_not_removed_when_overlapping() {
        // int ∧ ¬number — not redundant (Int <: Number, this is a contradiction,
        // but the negation itself is NOT redundant — it carries information).
        let members = vec![arc_ty!(Int), OutputTy::Neg(TyRef::from(arc_ty!(Number)))];
        let result = remove_redundant_negations(members.clone());
        assert_eq!(result, members);
    }

    // -- tautology detection for compound types -------------------------------

    #[test]
    fn tautology_attrset_neg_attrset() {
        // {x: int} ∨ ¬{x: int} → empty (tautology).
        let attrset = arc_ty!({ "x": Int });
        let members = vec![attrset.clone(), OutputTy::Neg(TyRef::from(attrset))];
        let result = remove_tautological_pairs(members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_list_neg_list() {
        // [int] ∨ ¬[int] → empty.
        let list = arc_ty!([Int]);
        let members = vec![list.clone(), OutputTy::Neg(TyRef::from(list))];
        let result = remove_tautological_pairs(members);
        assert!(result.is_empty());
    }

    #[test]
    fn tautology_compound_preserves_others() {
        // {x: int} ∨ ¬{x: int} ∨ string → string.
        let attrset = arc_ty!({ "x": Int });
        let members = vec![
            attrset.clone(),
            OutputTy::Neg(TyRef::from(attrset)),
            arc_ty!(String),
        ];
        let result = remove_tautological_pairs(members);
        assert_eq!(result, vec![arc_ty!(String)]);
    }

    // -- is_output_subtype_or_equal tests --------------------------------------

    #[test]
    fn subtype_int_number() {
        assert!(is_output_subtype_or_equal(&arc_ty!(Int), &arc_ty!(Number)));
    }

    #[test]
    fn subtype_float_number() {
        assert!(is_output_subtype_or_equal(
            &arc_ty!(Float),
            &arc_ty!(Number)
        ));
    }

    #[test]
    fn subtype_reflexive() {
        assert!(is_output_subtype_or_equal(&arc_ty!(Int), &arc_ty!(Int)));
        assert!(is_output_subtype_or_equal(
            &arc_ty!(String),
            &arc_ty!(String)
        ));
    }

    #[test]
    fn not_subtype_number_int() {
        // Number is NOT a subtype of Int — Number also includes Float.
        assert!(!is_output_subtype_or_equal(&arc_ty!(Number), &arc_ty!(Int)));
    }

    #[test]
    fn not_subtype_different_constructors() {
        assert!(!is_output_subtype_or_equal(&arc_ty!(Int), &arc_ty!(String)));
        assert!(!is_output_subtype_or_equal(
            &arc_ty!(Int),
            &arc_ty!({ "x": Int })
        ));
    }

    #[test]
    fn subtype_structural_equality_attrset() {
        let a = arc_ty!({ "x": Int });
        let b = arc_ty!({ "x": Int });
        assert!(is_output_subtype_or_equal(&a, &b));
    }

    // -- Regression: Number ∧ ¬Int is NOT a contradiction ----------------------

    #[test]
    fn no_contradiction_number_neg_int() {
        // Number ∧ ¬Int should NOT be a contradiction. Number includes Float,
        // so Number ∧ ¬Int = Float (a valid, inhabited type). The old
        // "not disjoint" check incorrectly flagged this as contradictory
        // because Number and Int overlap.
        let members = vec![arc_ty!(Number), OutputTy::Neg(TyRef::from(arc_ty!(Int)))];
        assert!(
            !has_type_contradiction(&members),
            "Number ∧ ¬Int should NOT be a contradiction (Number ⊄ Int)"
        );
    }

    #[test]
    fn no_contradiction_number_neg_float() {
        // Number ∧ ¬Float should NOT be a contradiction (Number ∧ ¬Float = Int).
        let members = vec![arc_ty!(Number), OutputTy::Neg(TyRef::from(arc_ty!(Float)))];
        assert!(
            !has_type_contradiction(&members),
            "Number ∧ ¬Float should NOT be a contradiction (Number ⊄ Float)"
        );
    }

    // -- OutputTy::Top tests -------------------------------------------------

    #[test]
    fn tautology_produces_top_in_positive_canonicalization() {
        // A variable whose lower bounds are `int` and `~int` produces a
        // tautology (int | ~int = ⊤). In positive position, this should
        // canonicalize to Top (any).
        use crate::storage::TypeStorage;
        use lang_ty::Ty;

        let mut table = TypeStorage::new();
        let var_id = table.new_var();
        let int_ty = table.new_concrete(Ty::Primitive(lang_ty::PrimitiveTy::Int));
        let neg_int = table.new_concrete(Ty::Neg(int_ty));

        table.add_lower_bound(var_id, int_ty);
        table.add_lower_bound(var_id, neg_int);

        let provenance = std::collections::HashMap::new();
        let result = canonicalize_standalone(&table, &provenance, var_id, Positive);
        assert_eq!(
            result,
            arc_ty!(Top),
            "int | ~int tautology should produce Top (any), got: {result}"
        );
    }

    #[test]
    fn top_displays_as_any() {
        let top = arc_ty!(Top);
        assert_eq!(top.to_string(), "any");
    }

    #[test]
    fn top_identity_for_has_type_contradiction() {
        // Top in a contradiction check should be ignored (like TyVar).
        let members = vec![
            arc_ty!(Top),
            arc_ty!(Int),
            OutputTy::Neg(TyRef::from(arc_ty!(String))),
        ];
        assert!(!has_type_contradiction(&members));
    }

    // -- absorb_subsumed_union_members tests ----------------------------------

    #[test]
    fn absorb_open_wildcard_absorbs_open_with_fields() {
        // { ... } | { setenv: a, ... } → { ... }
        // The bare open attrset subsumes any open attrset with more fields.
        let bare_open = arc_ty!({ ; ... });
        let specific_open = arc_ty!({ "setenv": String; ... });
        let members = vec![bare_open.clone(), specific_open];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![bare_open]);
    }

    #[test]
    fn absorb_closed_not_absorbed() {
        // Closed attrsets should never be absorbed.
        // { x: int } | { x: int, y: string } → unchanged (both closed).
        let a = arc_ty!({ "x": Int });
        let b = arc_ty!({ "x": Int, "y": String });
        let members = vec![a.clone(), b.clone()];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![a, b]);
    }

    #[test]
    fn absorb_partial_subsumption_keeps_both() {
        // { x: int, ... } | { y: string, ... } → unchanged (neither subsumes).
        let a = arc_ty!({ "x": Int; ... });
        let b = arc_ty!({ "y": String; ... });
        let members = vec![a.clone(), b.clone()];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![a, b]);
    }

    #[test]
    fn absorb_open_with_shared_fields() {
        // { x: int, ... } | { x: int, y: string, ... } → { x: int, ... }
        // The first subsumes the second (every required field of first is in second).
        let general = arc_ty!({ "x": Int; ... });
        let specific = arc_ty!({ "x": Int, "y": String; ... });
        let members = vec![general.clone(), specific];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![general]);
    }

    #[test]
    fn absorb_preserves_non_attrset_members() {
        // string | { ... } | { x: int, ... } → string | { ... }
        let bare_open = arc_ty!({ ; ... });
        let specific = arc_ty!({ "x": Int; ... });
        let members = vec![arc_ty!(String), bare_open.clone(), specific];
        let result = absorb_subsumed_union_members(members);
        assert_eq!(result, vec![arc_ty!(String), bare_open]);
    }

    // -- factor_shared_from_intersection tests --------------------------------

    #[test]
    fn factor_shared_basic() {
        // (A|C) & (B|C) → C | (A&B)
        // (int|string) & (bool|string) → string | (int & bool)
        let members = vec![
            OutputTy::Union(vec![
                TyRef::from(arc_ty!(Int)),
                TyRef::from(arc_ty!(String)),
            ]),
            OutputTy::Union(vec![
                TyRef::from(arc_ty!(Bool)),
                TyRef::from(arc_ty!(String)),
            ]),
        ];
        let result = factor_shared_from_intersection(members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        // The result should be a Union containing string and (int & bool).
        match &result[0] {
            OutputTy::Union(parts) => {
                assert_eq!(parts.len(), 2, "union should have 2 members: {parts:?}");
                // One should be string, the other an intersection of int & bool.
                let has_string = parts.iter().any(|p| *p.0 == arc_ty!(String));
                assert!(has_string, "should contain string");
                let has_intersection = parts
                    .iter()
                    .any(|p| matches!(&*p.0, OutputTy::Intersection(inner) if inner.len() == 2));
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
        // (int|string) & (bool|float) → unchanged (no shared members).
        let u1 = OutputTy::Union(vec![
            TyRef::from(arc_ty!(Int)),
            TyRef::from(arc_ty!(String)),
        ]);
        let u2 = OutputTy::Union(vec![
            TyRef::from(arc_ty!(Bool)),
            TyRef::from(arc_ty!(Float)),
        ]);
        let members = vec![u1.clone(), u2.clone()];
        let result = factor_shared_from_intersection(members);
        // Should reassemble as two union members unchanged.
        assert_eq!(result, vec![u1, u2]);
    }

    #[test]
    fn factor_fewer_than_two_unions_unchanged() {
        // Only one union member — nothing to factor.
        let u1 = OutputTy::Union(vec![
            TyRef::from(arc_ty!(Int)),
            TyRef::from(arc_ty!(String)),
        ]);
        let non_union = arc_ty!(Bool);
        let members = vec![u1.clone(), non_union.clone()];
        let result = factor_shared_from_intersection(members);
        assert_eq!(result, vec![non_union, u1]);
    }

    #[test]
    fn factor_mixed_union_and_non_union() {
        // (int|string) & (bool|string) & null → string | ((int & bool) & null)
        let members = vec![
            OutputTy::Union(vec![
                TyRef::from(arc_ty!(Int)),
                TyRef::from(arc_ty!(String)),
            ]),
            OutputTy::Union(vec![
                TyRef::from(arc_ty!(Bool)),
                TyRef::from(arc_ty!(String)),
            ]),
            arc_ty!(Null),
        ];
        let result = factor_shared_from_intersection(members);
        assert_eq!(result.len(), 1, "should produce single element: {result:?}");
        match &result[0] {
            OutputTy::Union(parts) => {
                assert_eq!(parts.len(), 2, "should have shared + remainder: {parts:?}");
                let has_string = parts.iter().any(|p| *p.0 == arc_ty!(String));
                assert!(has_string, "should contain shared string");
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }
}
