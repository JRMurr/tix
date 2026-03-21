// ==============================================================================
// Core Subtyping Constraint Function — the heart of SimpleSub
// ==============================================================================
//
// Instead of equality-based unification, we record directional subtyping:
// constrain(sub, sup) means "sub flows into sup" or "sub <: sup".
// When a variable appears on the left, it gains an upper bound.
// When a variable appears on the right, it gains a lower bound.
// This naturally supports union and intersection types.
//
// Bidirectional vs. directional constraints
// ------------------------------------------
// Some call sites use bidirectional constraints (both directions):
//   constrain(a, b); constrain(b, a);   // "a equals b"
// This is used when two types must be identical, e.g.:
// - Linking a name slot to its inferred type (name_slot ≡ inferred_ty)
// - Pattern match bindings (param ≡ destructured attrset)
// - Overload return type pinning (ret ≡ resolved_type)
//
// Other call sites use directional (one-way) constraints:
//   constrain(sub, sup);                // "sub flows into sup"
// This is used for genuine subtyping relationships:
// - Function application: arg <: param (argument is subtype of parameter)
// - If-then-else branches: then_ty <: result, else_ty <: result
// - List concat elements: lhs_elem <: result_elem, rhs_elem <: result_elem
//
// The distinction matters for type variable bounds: bidirectional constraints
// make both variables equivalent (same upper and lower bounds), while
// directional constraints preserve the subtyping relationship and naturally
// produce union/intersection types during canonicalization.

use super::{CheckCtx, InferenceError, LocatedError, TyId};

use crate::storage::TypeEntry;
use lang_ty::{
    arc_ty::OutputTy,
    disjoint::{are_shapes_disjoint, ConstructorShape},
    AttrSetTy, OwnedTy, Ty, TyRef, TypeArena,
};
use smallvec::SmallVec;
use smol_str::SmolStr;

/// Frozen lambda bodies with more than this many attrset fields get lazy
/// decomposition (separate Frozen wrappers for param/body). Below this
/// threshold, full interning preserves TyVar sharing for polymorphic types.
const FROZEN_LAMBDA_FIELD_THRESHOLD: usize = 64;

impl CheckCtx<'_> {
    /// Constrain sub <: sup, locating any error at the current expression.
    pub(crate) fn constrain_at(&mut self, sub: TyId, sup: TyId) -> Result<(), LocatedError> {
        self.constrain(sub, sup).map_err(|err| self.locate_err(err))
    }

    /// Constrain a ≡ b (bidirectional: a <: b and b <: a), locating any error
    /// at the current expression.
    pub(crate) fn constrain_equal(&mut self, a: TyId, b: TyId) -> Result<(), LocatedError> {
        self.constrain_at(a, b)?;
        self.constrain_at(b, a)
    }

    /// Record that `sub <: sup` — `sub` is a subtype of `sup`.
    pub fn constrain(&mut self, sub: TyId, sup: TyId) -> Result<(), InferenceError> {
        // Periodic RSS check inside the constraint propagation hotpath.
        // This catches cases where a single infer_expr call triggers a huge
        // constrain() cascade (e.g. structural subtyping on large attrsets).
        // `should_bail()` caches a positive result in `bailed_out`, so
        // the first check is O(1) for subsequent calls.
        if self.rss_limit_mb.is_some() {
            self.op_counter = self.op_counter.wrapping_add(1);
            if self.op_counter.is_multiple_of(Self::RSS_CHECK_INTERVAL) && self.should_bail() {
                log::warn!(
                    "inference aborted during constrain (after {} operations, {} cache entries, {} type slots)",
                    self.op_counter,
                    self.types.constrain_cache.len(),
                    self.types.storage.len(),
                );
                return Ok(());
            }
        } else if self.bailed_out {
            return Ok(());
        }

        // Reflexivity: identical ids are trivially subtypes.
        if sub == sup {
            return Ok(());
        }

        // Cycle detection: if we've already processed this (sub, sup) pair, skip.
        if !self.types.constrain_cache.insert((sub, sup)) {
            return Ok(());
        }

        // Guard against stack overflow: constrain() recurses through variable
        // bounds chains and structural children, which can be very deep on
        // complex type graphs.
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            // Check entry discriminants without cloning. We only clone the data
            // we actually need for each case: bounds Vecs for variables (cheap —
            // Vec<TyId> is Vec<u32>), or the full Ty for concrete types.
            let sub_is_var = self.types.is_var(sub);
            let sup_is_var = self.types.is_var(sup);

            match (sub_is_var, sup_is_var) {
                // sub is a variable — record sup as upper bound, propagate to existing lower bounds.
                (true, _) => {
                    // If this variable was pre-allocated for an expression, update
                    // current_expr so that any mismatch discovered during propagation
                    // is attributed to a specific sub-expression rather than a distant
                    // ancestor (e.g. the root lambda).
                    if let Some(expr) = self.expr_for_ty(sub) {
                        self.current_expr = expr;
                    }
                    self.types.storage.add_upper_bound(sub, sup);
                    // Clone just the bounds Vec (Vec<TyId> ~ Vec<u32>, cheap)
                    // to release the borrow on storage before recursive calls.
                    let lower_bounds = self
                        .types
                        .storage
                        .get_var(sub)
                        .expect("is_var(sub) was true but get_var(sub) returned None")
                        .lower_bounds
                        .clone();
                    for lb in lower_bounds {
                        self.constrain(lb, sup)?;
                    }
                    Ok(())
                }
                // sup is a variable — record sub as lower bound, propagate to existing upper bounds.
                (_, true) => {
                    if let Some(expr) = self.expr_for_ty(sup) {
                        self.current_expr = expr;
                    }
                    self.types.storage.add_lower_bound(sup, sub);
                    let upper_bounds = self
                        .types
                        .storage
                        .get_var(sup)
                        .expect("is_var(sup) was true but get_var(sup) returned None")
                        .upper_bounds
                        .clone();
                    for ub in upper_bounds {
                        self.constrain(sub, ub)?;
                    }
                    Ok(())
                }

                // Both concrete — structural subtyping. Clone only the Ty values.
                (false, false) => {
                    let sub_ty = self.types.expect_concrete(sub);
                    let sup_ty = self.types.expect_concrete(sup);
                    self.constrain_concrete(sub, sup, &sub_ty, &sup_ty)
                }
            }
        })
    }

    /// Structural subtyping between two concrete types.
    ///
    /// `sub_id`/`sup_id` are the original TyIds from `constrain()` — passed
    /// through so that Inter/Union decomposition reuses them instead of
    /// allocating fresh copies (which would defeat the constrain_cache).
    fn constrain_concrete(
        &mut self,
        sub_id: TyId,
        sup_id: TyId,
        sub: &Ty<TyId>,
        sup: &Ty<TyId>,
    ) -> Result<(), InferenceError> {
        match (sub, sup) {
            // Named is transparent — unwrap and constrain the inner type.
            (Ty::Named(_, inner), _) => self.constrain(*inner, sup_id),
            (_, Ty::Named(_, inner)) => self.constrain(sub_id, *inner),

            // ── Frozen import types: lazy materialization ──────────────────
            //
            // Frozen wraps an entire OutputTy tree in a single TyId. Instead
            // of eagerly interning all fields (O(N) TyId allocations), we
            // materialize only the parts actually demanded by constraints.

            // Frozen on LHS vs AttrSet on RHS: the hot path for large imports.
            // Only intern the fields the supertype demands.
            (Ty::Frozen(owned), Ty::AttrSet(sup_attr)) => {
                let owned = owned.clone();
                let sup_attr = sup_attr.clone();
                self.constrain_frozen_attrset(&owned, &sup_attr)
            }

            // Frozen on LHS vs Lambda on RHS: decompose structurally without
            // interning the entire tree.
            (
                Ty::Frozen(owned),
                Ty::Lambda {
                    param: sup_param,
                    body: sup_body,
                },
            ) => {
                let owned = owned.clone();
                let sup_param = *sup_param;
                let sup_body = *sup_body;
                self.constrain_frozen_lambda(&owned, sup_param, sup_body)
            }

            // Frozen on LHS, any other RHS: full interning fallback.
            (Ty::Frozen(owned), _) => {
                let owned = owned.clone();
                let interned = self.intern_output_ty(&owned);
                self.constrain(interned, sup_id)
            }

            // Lambda on LHS vs Frozen on RHS.
            (
                Ty::Lambda {
                    param: sub_param,
                    body: sub_body,
                },
                Ty::Frozen(owned),
            ) => {
                let owned = owned.clone();
                let sub_param = *sub_param;
                let sub_body = *sub_body;
                self.constrain_lambda_frozen(sub_param, sub_body, &owned)
            }

            // AttrSet on LHS vs Frozen on RHS: mirror of constrain_frozen_attrset.
            (Ty::AttrSet(sub_attr), Ty::Frozen(owned)) => {
                let owned = owned.clone();
                let sub_attr = sub_attr.clone();
                self.constrain_attrset_frozen(&sub_attr, &owned)
            }

            // Frozen on RHS: full interning fallback.
            (_, Ty::Frozen(owned)) => {
                let owned = owned.clone();
                let interned = self.intern_output_ty(&owned);
                self.constrain(sub_id, interned)
            }

            // Lambda: contravariant in param, covariant in body.
            (
                Ty::Lambda {
                    param: p1,
                    body: b1,
                },
                Ty::Lambda {
                    param: p2,
                    body: b2,
                },
            ) => {
                self.constrain(*p2, *p1)?; // contravariant
                self.constrain(*b1, *b2)?; // covariant
                Ok(())
            }

            // List: covariant in element type.
            //
            // Covariance is sound here because Nix is a pure language — lists
            // are immutable values. In a language with mutable list operations
            // (e.g. `list[0] = x`), covariance would be unsound: you could
            // alias a `List<Cat>` as `List<Animal>`, then write a `Dog` into
            // it through the `Animal` reference, violating the `Cat` invariant.
            // Nix has no such mutation, so `[Cat] <: [Animal]` is safe.
            (Ty::List(e1), Ty::List(e2)) => self.constrain(*e1, *e2),

            // AttrSet: width subtyping — sub must have all fields that sup requires.
            (Ty::AttrSet(sub_attr), Ty::AttrSet(sup_attr)) => {
                self.constrain_attrsets(sub_attr, sup_attr)
            }

            // Identical primitives are subtypes of each other.
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1 == p2 => Ok(()),
            // Primitive subtyping: Int <: Number, Float <: Number.
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1.is_subtype_of(p2) => Ok(()),

            // ── Negation rules (BAS) ────────────────────────────────────────
            //
            // Neg(A) <: Neg(B) iff B <: A (contravariant flip).
            (Ty::Neg(a), Ty::Neg(b)) => self.constrain(*b, *a),

            // Concrete <: Neg(inner): succeeds when the concrete type is
            // provably disjoint from the negated type. Handles all constructor
            // kinds — primitives, attrsets, lists, lambdas — not just primitives.
            // E.g. AttrSet <: ¬Null succeeds because attrsets and null are
            // disjoint constructors; Int <: ¬Null succeeds because Int ≠ Null.
            (sub, Ty::Neg(inner)) if !matches!(sub, Ty::Inter(..) | Ty::Union(..)) => {
                // Check disjointness without cloning the inner entry.
                let disjoint = matches!(
                    self.types.storage.get(*inner),
                    TypeEntry::Concrete(inner_ty) if are_types_disjoint(sub, inner_ty)
                );
                if disjoint {
                    Ok(())
                } else {
                    Err(InferenceError::TypeMismatch(Box::new((
                        sub.clone(),
                        sup.clone(),
                    ))))
                }
            }

            // ── Intersection / Union rules (MLstruct-style) ─────────────────

            // Intersection on RHS: V <: A ∧ B → V <: A and V <: B
            // Always decomposable regardless of what the sub-type is.
            (_, Ty::Inter(a, b)) => {
                let (a, b) = (*a, *b);
                // Reuse original sub_id — don't allocate a fresh copy.
                self.constrain(sub_id, a)?;
                self.constrain(sub_id, b)
            }

            // Union on LHS: A ∨ B <: V → A <: V and B <: V
            // Always decomposable regardless of what the super-type is.
            (Ty::Union(a, b), _) => {
                let (a, b) = (*a, *b);
                self.constrain(a, sup_id)?;
                self.constrain(b, sup_id)
            }

            // Intersection on LHS — the "annoying" case (MLstruct-style).
            // Variable isolation: when one member is a variable, move the
            // other across the <: boundary with negation flipped.
            //   α ∧ C <: U → α <: U ∨ ¬C
            (Ty::Inter(a, b), _) => {
                let (a, b) = (*a, *b);
                self.constrain_lhs_inter(a, b, sup_id, sup)
            }

            // Union on RHS: route concrete sub to the appropriate member.
            (_, Ty::Union(a, b)) => {
                let (a, b) = (*a, *b);
                self.constrain_rhs_union(sub, a, b, sub_id)
            }

            // ── __functor calling convention ──────────────────────────────
            //
            // In Nix, `{ __functor = self: x: body; ... }` can be called as
            // a function. When an AttrSet with a `__functor` field flows into
            // a Lambda constraint, we extract the functor and constrain it as
            // `self -> (param -> body)` where `self` is the attrset itself.
            (Ty::AttrSet(attr), Ty::Lambda { param, body })
                if attr.fields.contains_key("__functor") =>
            {
                let functor_ty = attr.fields["__functor"];
                // __functor has type `self -> arg -> result` in Nix.
                // Constrain: functor_ty <: (sub_id -> Lambda { param, body })
                let inner_lambda = self.alloc_concrete(Ty::Lambda {
                    param: *param,
                    body: *body,
                });
                let expected_functor = self.alloc_concrete(Ty::Lambda {
                    param: sub_id,
                    body: inner_lambda,
                });
                self.constrain(functor_ty, expected_functor)
            }

            // Type mismatch.
            _ => Err(InferenceError::TypeMismatch(Box::new((
                sub.clone(),
                sup.clone(),
            )))),
        }
    }

    /// `Inter(a, b) <: sup` — the "annoying" case. Use variable isolation
    /// (MLstruct-style) when one member is a variable.
    ///
    /// Before applying variable isolation, we check if the concrete member is
    /// provably disjoint from the super-type. If so, the intersection is
    /// uninhabitable and we fail immediately. This catches cases like
    /// `Inter(α, Null) <: String` where Null and String are disjoint.
    fn constrain_lhs_inter(
        &mut self,
        a: TyId,
        b: TyId,
        sup_id: TyId,
        sup: &Ty<TyId>,
    ) -> Result<(), InferenceError> {
        // Determine if each side contains a variable (possibly nested in Inter).
        let a_has_var = self.inter_contains_var(a);
        let b_has_var = self.inter_contains_var(b);
        let a_is_var = self.types.is_var(a);
        let b_is_var = self.types.is_var(b);

        match (
            a_is_var || (a_has_var && !b_has_var),
            b_is_var || (b_has_var && !a_has_var),
        ) {
            (true, false) => {
                // Check: if b is concrete and provably disjoint from sup.
                // For composed narrowing constraints (Inter(C1, C2)), check
                // recursively — if any leaf of the intersection is disjoint
                // from sup, the whole intersection is disjoint.
                if self.is_disjoint_from_sup(b, sup) {
                    return Err(InferenceError::TypeMismatch(Box::new((
                        Ty::Inter(a, b),
                        sup.clone(),
                    ))));
                }
                // α ∧ C <: U → α <: U ∨ ¬C (α side absorbs the constraint)
                let neg_b = self.alloc_concrete(Ty::Neg(b));
                // Union absorption: (A ∨ B) ∨ B = A ∨ B. If sup_id's union
                // tree already contains neg_b, skip wrapping — the constraint
                // is already captured. This prevents infinite growth when two
                // mutually-lower-bounded variables both carry Inter wrappers
                // (e.g. from narrowing), which would otherwise create ever-deeper
                // Union nesting with fresh TyIds that defeat the constrain_cache.
                let target = if self.union_contains_member(sup_id, neg_b) {
                    sup_id
                } else {
                    self.alloc_concrete(Ty::Union(sup_id, neg_b))
                };
                self.constrain(a, target)
            }
            (false, true) => {
                if self.is_disjoint_from_sup(a, sup) {
                    return Err(InferenceError::TypeMismatch(Box::new((
                        Ty::Inter(a, b),
                        sup.clone(),
                    ))));
                }
                // C ∧ α <: U → α <: U ∨ ¬C
                let neg_a = self.alloc_concrete(Ty::Neg(a));
                let target = if self.union_contains_member(sup_id, neg_a) {
                    sup_id
                } else {
                    self.alloc_concrete(Ty::Union(sup_id, neg_a))
                };
                self.constrain(b, target)
            }
            _ => {
                // Both have variables or neither — can't isolate cleanly.
                // Constrain each member individually. This is conservative
                // (over-constraining): it skips the disjointness check that
                // the variable-isolation paths perform. For example,
                // `Inter(α, String) <: Int` going through this path would
                // over-constrain α rather than detecting the disjointness.
                // This only triggers for nested Inter trees with variables
                // on both sides, which is rare in practice.
                // TODO: handle both-variable case with DNF decomposition.
                self.constrain(a, sup_id)?;
                self.constrain(b, sup_id)
            }
        }
    }

    /// Check if a TyId (possibly a composed Inter from narrowing) is provably
    /// disjoint from a super-type. For `Inter(A, B)`, if EITHER member is
    /// disjoint from sup, the intersection is disjoint (since `A ∧ B ⊆ A`).
    fn is_disjoint_from_sup(&self, id: TyId, sup: &Ty<TyId>) -> bool {
        match self.types.storage.get(id) {
            TypeEntry::Concrete(ty @ Ty::Inter(a, b)) => {
                let (a, b) = (*a, *b);
                // Check the Inter itself first (unlikely to match, but handles
                // exotic cases). Then recurse into members.
                are_types_disjoint(ty, sup)
                    || self.is_disjoint_from_sup(a, sup)
                    || self.is_disjoint_from_sup(b, sup)
            }
            TypeEntry::Concrete(ty) => are_types_disjoint(ty, sup),
            _ => false,
        }
    }

    /// Check if a TyId is or transitively contains a type variable
    /// (through Inter nesting). Used to find the variable side for
    /// MLstruct-style variable isolation. Results are cached since type
    /// entries are append-only (immutable once allocated).
    fn inter_contains_var(&mut self, id: TyId) -> bool {
        if let Some(&cached) = self.types.inter_var_cache.get(&id) {
            return cached;
        }
        let result = match self.types.storage.get(id) {
            TypeEntry::Variable(_) => true,
            TypeEntry::Concrete(Ty::Inter(a, b)) => {
                let (a, b) = (*a, *b);
                self.inter_contains_var(a) || self.inter_contains_var(b)
            }
            TypeEntry::Concrete(Ty::Named(_, inner)) => {
                let inner = *inner;
                self.inter_contains_var(inner)
            }
            _ => false,
        };
        self.types.inter_var_cache.insert(id, result);
        result
    }

    /// Check if a Union type tree contains a specific TyId as a leaf member.
    /// Used for union absorption: `(A ∨ B) ∨ B = A ∨ B`. When variable
    /// isolation creates `Union(sup, neg_c)` and sup already contains neg_c,
    /// wrapping would be redundant and cause infinite growth in cyclic variable
    /// chains.
    ///
    /// Only checks TyId equality (not structural equivalence), which is
    /// sufficient because `alloc_concrete(Neg(x))` is deduplicated via
    /// `neg_cache` — the same `Neg(x)` always returns the same TyId.
    /// Results are cached since Union structure is immutable once allocated.
    fn union_contains_member(&mut self, id: TyId, target: TyId) -> bool {
        if id == target {
            return true;
        }
        if self.types.union_member_cache.contains(&(id, target)) {
            return true;
        }
        let result = match self.types.storage.get(id) {
            TypeEntry::Concrete(Ty::Union(a, b)) => {
                let (a, b) = (*a, *b);
                self.union_contains_member(a, target) || self.union_contains_member(b, target)
            }
            TypeEntry::Concrete(Ty::Named(_, inner)) => {
                let inner = *inner;
                self.union_contains_member(inner, target)
            }
            _ => false,
        };
        if result {
            self.types.union_member_cache.insert((id, target));
        }
        result
    }

    /// `sub <: Union(a, b)` — route the sub-type to the correct union member.
    ///
    /// Uses a two-phase approach: try concrete match first, fall to variable.
    /// This avoids speculative constraint tries which would cause spurious
    /// bounds (the constrain_cache is non-rollbackable).
    fn constrain_rhs_union(
        &mut self,
        sub: &Ty<TyId>,
        a: TyId,
        b: TyId,
        sub_id: TyId,
    ) -> Result<(), InferenceError> {
        let a_is_var = self.types.is_var(a);
        let b_is_var = self.types.is_var(b);

        match (a_is_var, b_is_var) {
            // One variable, one concrete: route to concrete if compatible, else variable.
            (false, true) => {
                if is_concrete_compatible(sub, self.types.storage.get(a)) {
                    self.constrain(sub_id, a)
                } else {
                    self.constrain(sub_id, b)
                }
            }
            (true, false) => {
                if is_concrete_compatible(sub, self.types.storage.get(b)) {
                    self.constrain(sub_id, b)
                } else {
                    self.constrain(sub_id, a)
                }
            }
            // Both concrete: use disjointness analysis.
            (false, false) => {
                let a_ty = self.types.expect_concrete(a);
                let b_ty = self.types.expect_concrete(b);
                let disjoint_a = are_types_disjoint(sub, &a_ty);
                let disjoint_b = are_types_disjoint(sub, &b_ty);

                match (disjoint_a, disjoint_b) {
                    (true, false) => self.constrain(sub_id, b),
                    (false, true) => self.constrain(sub_id, a),
                    (true, true) => Err(InferenceError::TypeMismatch(Box::new((
                        sub.clone(),
                        Ty::Union(a, b),
                    )))),
                    (false, false) => {
                        // Tiebreaker: same-constructor match.
                        if discriminant_matches(sub, &a_ty) && !discriminant_matches(sub, &b_ty) {
                            self.constrain(sub_id, a)
                        } else if discriminant_matches(sub, &b_ty)
                            && !discriminant_matches(sub, &a_ty)
                        {
                            self.constrain(sub_id, b)
                        } else {
                            // Can't route deterministically — constrain to both.
                            // Sound but over-constraining.
                            // TODO: snapshot/rollback for full DNF generality.
                            self.constrain(sub_id, a)?;
                            self.constrain(sub_id, b)
                        }
                    }
                }
            }
            // Both variables: can't route deterministically.
            (true, true) => {
                // Conservative: constrain to both.
                self.constrain(sub_id, a)?;
                self.constrain(sub_id, b)
            }
        }
    }

    /// Width subtyping for attribute sets: the sub-type must have every field the super-type has,
    /// and each field must be a subtype. The sub-type can have extra fields (width subtyping).
    fn constrain_attrsets(
        &mut self,
        sub_attr: &AttrSetTy<TyId>,
        sup_attr: &AttrSetTy<TyId>,
    ) -> Result<(), InferenceError> {
        for (key, sup_field) in &sup_attr.fields {
            match sub_attr.fields.get(key) {
                Some(sub_field) => self.constrain(*sub_field, *sup_field)?,
                None => {
                    // If the sub has a dyn_ty, use it to satisfy the missing
                    // named field: dyn_ty represents the type of any field not
                    // explicitly listed, so sub.dyn_ty <: sup_field must hold.
                    if let Some(sub_dyn) = sub_attr.dyn_ty {
                        self.constrain(sub_dyn, *sup_field)?;
                    } else if !sub_attr.open && !sup_attr.optional_fields.contains(key) {
                        // Skip the error if the field is optional in the supertype
                        // (it has a default value in the lambda pattern).
                        return Err(InferenceError::MissingField {
                            field: key.clone(),
                            available: sub_attr.fields.keys().cloned().collect(),
                        });
                    }
                    // Open attrsets intentionally pass here: the unknown "rest"
                    // portion may contain the required field. This is sound for
                    // pattern-match destructuring (`{ x, ... }: x`) where extra
                    // fields are expected.
                    //
                    // PendingHasField constraints (emitted at Select sites in
                    // infer_expr.rs) provide a second-chance check: after merges
                    // and overloads resolve, resolve_pending re-validates field
                    // presence on any attrset that became concrete or closed.
                }
            }
        }

        // Propagate dyn_ty constraints: if both attrsets have a dynamic field
        // type, the sub's dyn_ty must be a subtype of the sup's dyn_ty.
        if let (Some(sub_dyn), Some(sup_dyn)) = (sub_attr.dyn_ty, sup_attr.dyn_ty) {
            self.constrain(sub_dyn, sup_dyn)?;
        }

        Ok(())
    }

    /// Lazy field-level materialization for `Frozen(OutputTy) <: AttrSet`.
    ///
    /// Instead of interning the entire frozen OutputTy (which may have hundreds
    /// of fields), only intern the specific fields demanded by the supertype's
    /// attrset. This is the hot path for large imports like `lib/default.nix`
    /// where the importer accesses a small subset of fields.
    fn constrain_frozen_attrset(
        &mut self,
        owned: &OwnedTy,
        sup_attr: &AttrSetTy<TyId>,
    ) -> Result<(), InferenceError> {
        // Unwrap Named wrappers to find the structural type inside.
        let root = owned.arena.unwrap_named(owned.root);
        let inner = owned.arena.get(root);

        match inner {
            OutputTy::AttrSet(frozen_attr) => {
                let frozen_attr = frozen_attr.clone();
                // For each field demanded by the supertype, look it up in the
                // frozen attrset and intern just that field's type.
                for (key, sup_field) in &sup_attr.fields {
                    match frozen_attr.fields.get(key) {
                        Some(&frozen_field_ref) => {
                            let field_owned = OwnedTy::new(owned.arena.clone(), frozen_field_ref);
                            let field_ty = self.intern_frozen_owned_ty(&field_owned);
                            self.constrain(field_ty, *sup_field)?;
                        }
                        None => {
                            if let Some(frozen_dyn) = frozen_attr.dyn_ty {
                                let dyn_owned = OwnedTy::new(owned.arena.clone(), frozen_dyn);
                                let dyn_ty = self.intern_frozen_owned_ty(&dyn_owned);
                                self.constrain(dyn_ty, *sup_field)?;
                            } else if !frozen_attr.open && !sup_attr.optional_fields.contains(key) {
                                return Err(InferenceError::MissingField {
                                    field: key.clone(),
                                    available: frozen_attr.fields.keys().cloned().collect(),
                                });
                            }
                        }
                    }
                }

                // Propagate dyn_ty constraints.
                if let (Some(frozen_dyn), Some(sup_dyn)) = (frozen_attr.dyn_ty, sup_attr.dyn_ty) {
                    let dyn_owned = OwnedTy::new(owned.arena.clone(), frozen_dyn);
                    let dyn_ty = self.intern_frozen_owned_ty(&dyn_owned);
                    self.constrain(dyn_ty, sup_dyn)?;
                }

                Ok(())
            }
            _ => {
                let interned = self.intern_output_ty(owned);
                let sup_id = self.alloc_concrete(Ty::AttrSet(sup_attr.clone()));
                self.constrain(interned, sup_id)
            }
        }
    }

    /// Lazy structural decomposition for `Frozen(OutputTy) <: Lambda`.
    ///
    /// For large imported types (e.g. hackage-packages.nix returning a 16K-field
    /// attrset), interning the entire tree is prohibitively expensive. This method
    /// decomposes the lambda structurally, keeping param and body as separate
    /// Frozen wrappers so the massive body stays opaque until fields are demanded.
    ///
    /// For small types, falls back to full interning to preserve TyVar sharing
    /// across param and body (needed for polymorphic functions like `x: x`).
    fn constrain_frozen_lambda(
        &mut self,
        owned: &OwnedTy,
        sup_param: TyId,
        sup_body: TyId,
    ) -> Result<(), InferenceError> {
        let root = owned.arena.unwrap_named(owned.root);
        let inner = owned.arena.get(root);

        match inner {
            OutputTy::Lambda { param, body } => {
                let (param, body) = (*param, *body);
                if output_ty_field_count_arena(&owned.arena, body) > FROZEN_LAMBDA_FIELD_THRESHOLD {
                    let param_owned = OwnedTy::new(owned.arena.clone(), param);
                    let frozen_param = self.intern_frozen_owned_ty(&param_owned);
                    self.constrain(sup_param, frozen_param)?;
                    let body_owned = OwnedTy::new(owned.arena.clone(), body);
                    let frozen_body = self.intern_frozen_owned_ty(&body_owned);
                    self.constrain(frozen_body, sup_body)?;
                    Ok(())
                } else {
                    let interned = self.intern_output_ty(owned);
                    let sup_id = self.alloc_concrete(Ty::Lambda {
                        param: sup_param,
                        body: sup_body,
                    });
                    self.constrain(interned, sup_id)
                }
            }
            _ => {
                let interned = self.intern_output_ty(owned);
                let sup_id = self.alloc_concrete(Ty::Lambda {
                    param: sup_param,
                    body: sup_body,
                });
                self.constrain(interned, sup_id)
            }
        }
    }

    /// Mirror of `constrain_frozen_lambda` for `Lambda <: Frozen(OwnedTy)`.
    fn constrain_lambda_frozen(
        &mut self,
        sub_param: TyId,
        sub_body: TyId,
        owned: &OwnedTy,
    ) -> Result<(), InferenceError> {
        let root = owned.arena.unwrap_named(owned.root);
        let inner = owned.arena.get(root);

        match inner {
            OutputTy::Lambda { param, body } => {
                let (param, body) = (*param, *body);
                if output_ty_field_count_arena(&owned.arena, body) > FROZEN_LAMBDA_FIELD_THRESHOLD {
                    let param_owned = OwnedTy::new(owned.arena.clone(), param);
                    let frozen_param = self.intern_frozen_owned_ty(&param_owned);
                    self.constrain(frozen_param, sub_param)?;
                    let body_owned = OwnedTy::new(owned.arena.clone(), body);
                    let frozen_body = self.intern_frozen_owned_ty(&body_owned);
                    self.constrain(sub_body, frozen_body)?;
                    Ok(())
                } else {
                    let interned = self.intern_output_ty(owned);
                    let sub_id = self.alloc_concrete(Ty::Lambda {
                        param: sub_param,
                        body: sub_body,
                    });
                    self.constrain(sub_id, interned)
                }
            }
            _ => {
                let interned = self.intern_output_ty(owned);
                let sub_id = self.alloc_concrete(Ty::Lambda {
                    param: sub_param,
                    body: sub_body,
                });
                self.constrain(sub_id, interned)
            }
        }
    }

    /// Lazy field-level materialization for `AttrSet <: Frozen(OutputTy)`.
    ///
    /// Mirror of `constrain_frozen_attrset`. For each field in the sub attrset,
    /// look it up in the frozen attrset and constrain field-by-field without
    /// interning the entire frozen type.
    fn constrain_attrset_frozen(
        &mut self,
        sub_attr: &AttrSetTy<TyId>,
        owned: &OwnedTy,
    ) -> Result<(), InferenceError> {
        let root = owned.arena.unwrap_named(owned.root);
        let inner = owned.arena.get(root);

        match inner {
            OutputTy::AttrSet(frozen_attr) => {
                let frozen_attr = frozen_attr.clone();
                // For each field in the sub attrset, constrain against the
                // corresponding frozen field.
                for (key, &sub_field) in &sub_attr.fields {
                    if let Some(&frozen_field_ref) = frozen_attr.fields.get(key) {
                        let field_owned = OwnedTy::new(owned.arena.clone(), frozen_field_ref);
                        let field_ty = self.intern_frozen_owned_ty(&field_owned);
                        self.constrain(sub_field, field_ty)?;
                    }
                    // If the frozen attrset doesn't have this field but is open,
                    // that's fine — no constraint needed.
                }

                // Propagate dyn_ty constraints.
                if let (Some(sub_dyn), Some(frozen_dyn)) = (sub_attr.dyn_ty, frozen_attr.dyn_ty) {
                    let dyn_owned = OwnedTy::new(owned.arena.clone(), frozen_dyn);
                    let dyn_ty = self.intern_frozen_owned_ty(&dyn_owned);
                    self.constrain(sub_dyn, dyn_ty)?;
                }

                Ok(())
            }
            _ => {
                let interned = self.intern_output_ty(owned);
                let sup_id = self.alloc_concrete(Ty::AttrSet(sub_attr.clone()));
                self.constrain(sup_id, interned)
            }
        }
    }
}

/// Check if sub could be a subtype of target based on constructor shape.
/// Read-only — no side effects. Used by `constrain_rhs_union` to decide
/// which union member to route a concrete sub-type to.
fn is_concrete_compatible(sub: &Ty<TyId>, target: &TypeEntry) -> bool {
    // Named and Frozen are transparent/opaque — conservatively compatible.
    let sub = match sub {
        Ty::Named(_, _) | Ty::Frozen(_) => return true,
        other => other,
    };
    match target {
        TypeEntry::Variable(_) => true,
        TypeEntry::Concrete(Ty::Named(_, _) | Ty::Frozen(_)) => true, // conservative
        TypeEntry::Concrete(target_ty) => {
            discriminant_matches(sub, target_ty)
                || matches!(
                    (sub, target_ty),
                    (Ty::Primitive(p1), Ty::Primitive(p2)) if p1.is_subtype_of(p2)
                )
                // __functor attrsets are compatible with Lambda targets.
                || matches!(
                    (sub, target_ty),
                    (Ty::AttrSet(attr), Ty::Lambda { .. }) if attr.fields.contains_key("__functor")
                )
        }
    }
}

/// Check if two types have the same top-level constructor (discriminant).
fn discriminant_matches(a: &Ty<TyId>, b: &Ty<TyId>) -> bool {
    std::mem::discriminant(a) == std::mem::discriminant(b)
}

/// Check whether two concrete types are provably disjoint (their intersection
/// is uninhabited). Delegates to the shared `are_shapes_disjoint` logic in
/// `lang_ty::disjoint`.
///
/// See `lang_ty::disjoint::are_shapes_disjoint` for the full disjointness rules.
fn are_types_disjoint(a: &Ty<TyId>, b: &Ty<TyId>) -> bool {
    // Named is transparent, but we can't dereference TyId here (no storage
    // access), so Named conservatively falls through to Opaque below. This is
    // sound but could be refined if needed.

    // Collect field keys as sorted slices — avoids building a throwaway
    // BTreeMap<SmolStr, ()> just to check key membership.
    let a_keys: SmallVec<[SmolStr; 8]>;
    let b_keys: SmallVec<[SmolStr; 8]>;

    let a_shape = match a {
        Ty::Primitive(p) => ConstructorShape::Primitive(*p),
        Ty::AttrSet(attr) => {
            a_keys = attr.fields.keys().cloned().collect();
            ConstructorShape::AttrSet {
                field_keys: &a_keys,
                open: attr.open,
                optional: &attr.optional_fields,
            }
        }
        Ty::List(_) => ConstructorShape::List,
        Ty::Lambda { .. } => ConstructorShape::Lambda,
        // Named falls through to Opaque — conservative (never claims disjoint).
        _ => ConstructorShape::Opaque,
    };

    let b_shape = match b {
        Ty::Primitive(p) => ConstructorShape::Primitive(*p),
        Ty::AttrSet(attr) => {
            b_keys = attr.fields.keys().cloned().collect();
            ConstructorShape::AttrSet {
                field_keys: &b_keys,
                open: attr.open,
                optional: &attr.optional_fields,
            }
        }
        Ty::List(_) => ConstructorShape::List,
        Ty::Lambda { .. } => ConstructorShape::Lambda,
        _ => ConstructorShape::Opaque,
    };

    are_shapes_disjoint(&a_shape, &b_shape)
}

/// Count the total number of attrset fields reachable from an OutputTy.
/// Used to decide whether a Frozen lambda body is "large" enough to warrant
/// lazy decomposition. Stops counting at the threshold to avoid traversing
/// the entire tree for very large types.
fn output_ty_field_count_arena(arena: &TypeArena, ty: TyRef) -> usize {
    output_ty_field_count_inner_arena(arena, ty, FROZEN_LAMBDA_FIELD_THRESHOLD + 1)
}

fn output_ty_field_count_inner_arena(arena: &TypeArena, ty: TyRef, budget: usize) -> usize {
    if budget == 0 {
        return 0;
    }
    match &arena[ty] {
        OutputTy::AttrSet(attr) => attr.fields.len(),
        OutputTy::Lambda { param, body } => {
            let (param, body) = (*param, *body);
            let p = output_ty_field_count_inner_arena(arena, param, budget);
            let b = output_ty_field_count_inner_arena(arena, body, budget.saturating_sub(p));
            p + b
        }
        OutputTy::Named(_, inner) | OutputTy::List(inner) | OutputTy::Neg(inner) => {
            let inner = *inner;
            output_ty_field_count_inner_arena(arena, inner, budget)
        }
        OutputTy::Union(members) | OutputTy::Intersection(members) => {
            let members = members.clone();
            let mut total = 0;
            for m in &members {
                total += output_ty_field_count_inner_arena(arena, *m, budget.saturating_sub(total));
                if total > budget {
                    return total;
                }
            }
            total
        }
        _ => 0,
    }
}
