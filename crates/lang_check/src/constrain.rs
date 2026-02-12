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
use lang_ty::{AttrSetTy, Ty};

impl CheckCtx<'_> {
    /// Record that `sub <: sup` — `sub` is a subtype of `sup`.
    pub fn constrain(&mut self, sub: TyId, sup: TyId) -> Result<(), InferenceError> {
        // Reflexivity: identical ids are trivially subtypes.
        if sub == sup {
            return Ok(());
        }

        // Cycle detection: if we've already processed this (sub, sup) pair, skip.
        if !self.constrain_cache.insert((sub, sup)) {
            return Ok(());
        }

        // Clone entries to avoid borrow conflicts with &mut self.
        let sub_entry = self.table.get(sub).clone();
        let sup_entry = self.table.get(sup).clone();

        match (&sub_entry, &sup_entry) {
            // sub is a variable — record sup as upper bound, propagate to existing lower bounds.
            (TypeEntry::Variable(_), _) => {
                self.table.add_upper_bound(sub, sup);
                let lower_bounds = self.table.get_var(sub).unwrap().lower_bounds.clone();
                for lb in lower_bounds {
                    self.constrain(lb, sup)?;
                }
                Ok(())
            }
            // sup is a variable — record sub as lower bound, propagate to existing upper bounds.
            (_, TypeEntry::Variable(_)) => {
                self.table.add_lower_bound(sup, sub);
                let upper_bounds = self.table.get_var(sup).unwrap().upper_bounds.clone();
                for ub in upper_bounds {
                    self.constrain(sub, ub)?;
                }
                Ok(())
            }

            // Both concrete — structural subtyping.
            (TypeEntry::Concrete(sub_ty), TypeEntry::Concrete(sup_ty)) => {
                let sub_ty = sub_ty.clone();
                let sup_ty = sup_ty.clone();
                self.constrain_concrete(&sub_ty, &sup_ty)
            }
        }
    }

    /// Structural subtyping between two concrete types.
    fn constrain_concrete(&mut self, sub: &Ty<TyId>, sup: &Ty<TyId>) -> Result<(), InferenceError> {
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
            (Ty::List(e1), Ty::List(e2)) => self.constrain(*e1, *e2),

            // AttrSet: width subtyping — sub must have all fields that sup requires.
            (Ty::AttrSet(sub_attr), Ty::AttrSet(sup_attr)) => {
                self.constrain_attrsets(sub_attr, sup_attr)
            }

            // Identical primitives are subtypes of each other.
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1 == p2 => Ok(()),
            // Primitive subtyping: Int <: Number, Float <: Number.
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1.is_subtype_of(p2) => Ok(()),

            // Type mismatch.
            _ => Err(InferenceError::TypeMismatch(sub.clone(), sup.clone())),
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
                    // sub is missing a field that sup requires.
                    // If sub is open, that's still an error at the constraint level —
                    // it means the field is simply not known to exist.
                    // (The caller ensures open attrsets are used appropriately.)
                    if !sub_attr.open {
                        return Err(InferenceError::MissingField(key.clone()));
                    }
                    // If sub is open, we can't prove the field exists yet.
                    // For now we allow it — the field may come from the unknown rest.
                    // TODO: track this more precisely with "has-field" constraints.
                }
            }
        }
        Ok(())
    }
}
