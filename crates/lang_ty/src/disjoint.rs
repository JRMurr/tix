// ==============================================================================
// Constructor-Shape Disjointness
// ==============================================================================
//
// Shared disjointness logic for both the inference representation (Ty<TyId>)
// and the canonical output representation (OutputTy). Both types project into
// the same ConstructorShape enum, and a single `are_shapes_disjoint` function
// implements the disjointness rules once.
//
// Disjointness means the intersection of two types is uninhabited. This is
// used by:
// - constrain.rs: `Concrete <: Neg(inner)` succeeds when sub and inner are disjoint
// - collect.rs: redundant negation removal and contradiction detection

use std::collections::{BTreeMap, BTreeSet};

use smol_str::SmolStr;

use crate::PrimitiveTy;

/// A projection of a type's top-level constructor, carrying only the
/// information needed for disjointness checks (field keys and openness
/// for attrsets, nothing for lists/lambdas).
pub enum ConstructorShape<'a> {
    Primitive(PrimitiveTy),
    AttrSet {
        fields: &'a BTreeMap<SmolStr, ()>,
        open: bool,
        optional: &'a BTreeSet<SmolStr>,
    },
    List,
    Lambda,
    /// Inter/Union/Neg/TyVar or other non-constructor shapes — disjointness
    /// cannot be determined statically.
    Opaque,
}

/// Check whether two constructor shapes are provably disjoint (their
/// intersection is uninhabited).
///
/// Disjointness rules:
/// - **Different constructor kinds** → always disjoint. A primitive can never
///   be an attrset, list, or lambda, and vice versa.
/// - **Both primitives** → disjoint when neither is a subtype of the other.
///   `Int` and `String` are disjoint, but `Int` and `Number` overlap
///   (`Int ⊂ Number`).
/// - **Two attrsets** → disjoint when one is closed and the other requires a
///   field the closed one doesn't have. Otherwise conservatively not disjoint.
/// - **Same compound constructor (list, lambda)** → conservatively not disjoint.
/// - **Opaque on either side** → can't determine statically.
pub fn are_shapes_disjoint(a: &ConstructorShape, b: &ConstructorShape) -> bool {
    use ConstructorShape::*;
    match (a, b) {
        // Both primitives: disjoint when no overlap in the subtype lattice.
        (Primitive(p1), Primitive(p2)) => {
            p1 != p2 && !p1.is_subtype_of(p2) && !p2.is_subtype_of(p1)
        }

        // Different constructor kinds — always disjoint.
        (Primitive(_), AttrSet { .. })
        | (Primitive(_), List)
        | (Primitive(_), Lambda)
        | (AttrSet { .. }, Primitive(_))
        | (AttrSet { .. }, List)
        | (AttrSet { .. }, Lambda)
        | (List, Primitive(_))
        | (List, AttrSet { .. })
        | (List, Lambda)
        | (Lambda, Primitive(_))
        | (Lambda, AttrSet { .. })
        | (Lambda, List) => true,

        // Two attrsets: disjoint if one is closed and the other requires a field
        // the closed one doesn't have (a required field is one that's present in
        // `fields` but not in `optional`).
        (
            AttrSet {
                fields: a_fields,
                open: a_open,
                optional: _a_opt,
            },
            AttrSet {
                fields: b_fields,
                open: b_open,
                optional: b_opt,
            },
        ) => {
            if !a_open {
                for field in b_fields.keys() {
                    if !a_fields.contains_key(field) && !b_opt.contains(field) {
                        return true;
                    }
                }
            }
            if !b_open {
                for field in a_fields.keys() {
                    if !b_fields.contains_key(field) && !_a_opt.contains(field) {
                        return true;
                    }
                }
            }
            false
        }

        // Same compound constructor — conservatively not disjoint.
        (List, List) | (Lambda, Lambda) => false,

        // Opaque on either side — can't determine statically.
        (Opaque, _) | (_, Opaque) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prim(p: PrimitiveTy) -> ConstructorShape<'static> {
        ConstructorShape::Primitive(p)
    }

    #[test]
    fn disjoint_different_primitives() {
        assert!(are_shapes_disjoint(
            &prim(PrimitiveTy::Int),
            &prim(PrimitiveTy::String)
        ));
    }

    #[test]
    fn not_disjoint_same_primitive() {
        assert!(!are_shapes_disjoint(
            &prim(PrimitiveTy::Int),
            &prim(PrimitiveTy::Int)
        ));
    }

    #[test]
    fn not_disjoint_subtype_primitives() {
        assert!(!are_shapes_disjoint(
            &prim(PrimitiveTy::Int),
            &prim(PrimitiveTy::Number)
        ));
        assert!(!are_shapes_disjoint(
            &prim(PrimitiveTy::Number),
            &prim(PrimitiveTy::Int)
        ));
    }

    #[test]
    fn disjoint_cross_constructor() {
        assert!(are_shapes_disjoint(
            &prim(PrimitiveTy::Int),
            &ConstructorShape::List
        ));
        assert!(are_shapes_disjoint(
            &ConstructorShape::AttrSet {
                fields: &BTreeMap::new(),
                open: false,
                optional: &BTreeSet::new(),
            },
            &prim(PrimitiveTy::Null)
        ));
        assert!(are_shapes_disjoint(
            &ConstructorShape::List,
            &ConstructorShape::Lambda
        ));
    }

    #[test]
    fn not_disjoint_opaque() {
        assert!(!are_shapes_disjoint(
            &ConstructorShape::Opaque,
            &prim(PrimitiveTy::Int)
        ));
    }
}
