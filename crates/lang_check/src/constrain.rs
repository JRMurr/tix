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

use super::{CheckCtx, InferenceError, TyId};
use crate::storage::TypeEntry;
use lang_ty::{
    disjoint::{are_shapes_disjoint, ConstructorShape},
    AttrSetTy, Ty,
};

impl CheckCtx<'_> {
    /// Record that `sub <: sup` — `sub` is a subtype of `sup`.
    pub fn constrain(&mut self, sub: TyId, sup: TyId) -> Result<(), InferenceError> {
        // Reflexivity: identical ids are trivially subtypes.
        if sub == sup {
            return Ok(());
        }

        // Cycle detection: if we've already processed this (sub, sup) pair, skip.
        if !self.types.constrain_cache.insert((sub, sup)) {
            return Ok(());
        }

        // Clone entries to avoid borrow conflicts with &mut self.
        let sub_entry = self.types.storage.get(sub).clone();
        let sup_entry = self.types.storage.get(sup).clone();

        match (&sub_entry, &sup_entry) {
            // sub is a variable — record sup as upper bound, propagate to existing lower bounds.
            (TypeEntry::Variable(_), _) => {
                // If this variable was pre-allocated for an expression, update
                // current_expr so that any mismatch discovered during propagation
                // is attributed to a specific sub-expression rather than a distant
                // ancestor (e.g. the root lambda).
                if let Some(expr) = self.expr_for_ty(sub) {
                    self.current_expr = expr;
                }
                self.types.storage.add_upper_bound(sub, sup);
                let lower_bounds = self
                    .types
                    .storage
                    .get_var(sub)
                    .unwrap()
                    .lower_bounds
                    .clone();
                for lb in lower_bounds {
                    self.constrain(lb, sup)?;
                }
                Ok(())
            }
            // sup is a variable — record sub as lower bound, propagate to existing upper bounds.
            (_, TypeEntry::Variable(_)) => {
                if let Some(expr) = self.expr_for_ty(sup) {
                    self.current_expr = expr;
                }
                self.types.storage.add_lower_bound(sup, sub);
                let upper_bounds = self
                    .types
                    .storage
                    .get_var(sup)
                    .unwrap()
                    .upper_bounds
                    .clone();
                for ub in upper_bounds {
                    self.constrain(sub, ub)?;
                }
                Ok(())
            }

            // Both concrete — structural subtyping.
            (TypeEntry::Concrete(sub_ty), TypeEntry::Concrete(sup_ty)) => {
                let sub_ty = sub_ty.clone();
                let sup_ty = sup_ty.clone();
                self.constrain_concrete(sub, sup, &sub_ty, &sup_ty)
            }
        }
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
                match self.types.storage.get(*inner).clone() {
                    TypeEntry::Concrete(inner_ty) => {
                        if are_types_disjoint(sub, &inner_ty) {
                            Ok(())
                        } else {
                            Err(InferenceError::TypeMismatch(Box::new((
                                sub.clone(),
                                sup.clone(),
                            ))))
                        }
                    }
                    // Inner is a variable — conservatively fail.
                    _ => Err(InferenceError::TypeMismatch(Box::new((
                        sub.clone(),
                        sup.clone(),
                    )))),
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
        let a_is_var = matches!(self.types.storage.get(a), TypeEntry::Variable(_));
        let b_is_var = matches!(self.types.storage.get(b), TypeEntry::Variable(_));

        match (
            a_is_var || (a_has_var && !b_has_var),
            b_is_var || (b_has_var && !a_has_var),
        ) {
            (true, false) => {
                // Check: if b is concrete and provably disjoint from sup.
                if let TypeEntry::Concrete(b_ty) = self.types.storage.get(b).clone() {
                    if are_types_disjoint(&b_ty, sup) {
                        return Err(InferenceError::TypeMismatch(Box::new((
                            Ty::Inter(a, b),
                            sup.clone(),
                        ))));
                    }
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
                if let TypeEntry::Concrete(a_ty) = self.types.storage.get(a).clone() {
                    if are_types_disjoint(&a_ty, sup) {
                        return Err(InferenceError::TypeMismatch(Box::new((
                            Ty::Inter(a, b),
                            sup.clone(),
                        ))));
                    }
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
                // Constrain each member individually. This is conservative.
                self.constrain(a, sup_id)?;
                self.constrain(b, sup_id)
            }
        }
    }

    /// Check if a TyId is or transitively contains a type variable
    /// (through Inter nesting). Used to find the variable side for
    /// MLstruct-style variable isolation.
    fn inter_contains_var(&self, id: TyId) -> bool {
        match self.types.storage.get(id) {
            TypeEntry::Variable(_) => true,
            TypeEntry::Concrete(Ty::Inter(a, b)) => {
                self.inter_contains_var(*a) || self.inter_contains_var(*b)
            }
            _ => false,
        }
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
    fn union_contains_member(&self, id: TyId, target: TyId) -> bool {
        if id == target {
            return true;
        }
        match self.types.storage.get(id) {
            TypeEntry::Concrete(Ty::Union(a, b)) => {
                self.union_contains_member(*a, target) || self.union_contains_member(*b, target)
            }
            _ => false,
        }
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
        let a_is_var = matches!(self.types.storage.get(a), TypeEntry::Variable(_));
        let b_is_var = matches!(self.types.storage.get(b), TypeEntry::Variable(_));

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
                let a_ty = match self.types.storage.get(a) {
                    TypeEntry::Concrete(t) => t.clone(),
                    _ => unreachable!(),
                };
                let b_ty = match self.types.storage.get(b) {
                    TypeEntry::Concrete(t) => t.clone(),
                    _ => unreachable!(),
                };
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
                    // Skip the error if the field is optional in the supertype
                    // (it has a default value in the lambda pattern).
                    if !sub_attr.open && !sup_attr.optional_fields.contains(key) {
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
        Ok(())
    }
}

/// Check if sub could be a subtype of target based on constructor shape.
/// Read-only — no side effects. Used by `constrain_rhs_union` to decide
/// which union member to route a concrete sub-type to.
fn is_concrete_compatible(sub: &Ty<TyId>, target: &TypeEntry) -> bool {
    match target {
        TypeEntry::Variable(_) => true,
        TypeEntry::Concrete(target_ty) => {
            discriminant_matches(sub, target_ty)
                || matches!(
                    (sub, target_ty),
                    (Ty::Primitive(p1), Ty::Primitive(p2)) if p1.is_subtype_of(p2)
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
    // Build owned key maps for attrset shapes. These are allocated only when
    // both types need shape projection (which involves attrsets).
    let a_keys;
    let b_keys;

    let a_shape = match a {
        Ty::Primitive(p) => ConstructorShape::Primitive(*p),
        Ty::AttrSet(attr) => {
            a_keys = attr.fields.keys().map(|k| (k.clone(), ())).collect();
            ConstructorShape::AttrSet {
                fields: &a_keys,
                open: attr.open,
                optional: &attr.optional_fields,
            }
        }
        Ty::List(_) => ConstructorShape::List,
        Ty::Lambda { .. } => ConstructorShape::Lambda,
        _ => ConstructorShape::Opaque,
    };

    let b_shape = match b {
        Ty::Primitive(p) => ConstructorShape::Primitive(*p),
        Ty::AttrSet(attr) => {
            b_keys = attr.fields.keys().map(|k| (k.clone(), ())).collect();
            ConstructorShape::AttrSet {
                fields: &b_keys,
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
