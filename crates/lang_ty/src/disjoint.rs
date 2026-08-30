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

use std::collections::BTreeSet;

use smol_str::SmolStr;

use crate::PrimitiveTy;

/// A projection of a type's top-level constructor, carrying only the
/// information needed for disjointness checks (field keys and openness
/// for attrsets, nothing for lists/lambdas).
///
/// `field_keys` is a pre-collected sorted slice of attrset field names,
/// avoiding the need to build a throwaway `BTreeMap<SmolStr, ()>` just
/// to check key membership.
pub enum ConstructorShape<'a> {
    Primitive(PrimitiveTy),
    AttrSet {
        field_keys: &'a [SmolStr],
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

        // Different constructor kinds — always disjoint, except AttrSet
        // with `__functor` vs Lambda (Nix's callable attrset convention).
        (Primitive(_), AttrSet { .. })
        | (Primitive(_), List)
        | (Primitive(_), Lambda)
        | (AttrSet { .. }, Primitive(_))
        | (AttrSet { .. }, List)
        | (List, Primitive(_))
        | (List, AttrSet { .. })
        | (List, Lambda)
        | (Lambda, Primitive(_))
        | (Lambda, List) => true,

        // AttrSet vs Lambda: disjoint unless the attrset has a `__functor`
        // field, which makes it callable in Nix.
        (AttrSet { field_keys, .. }, Lambda) | (Lambda, AttrSet { field_keys, .. }) => {
            !field_keys.contains(&SmolStr::from("__functor"))
        }

        // Two attrsets: disjoint if one is closed and the other requires a field
        // the closed one doesn't have (a required field is one that's present in
        // `field_keys` but not in `optional`).
        (
            AttrSet {
                field_keys: a_keys,
                open: a_open,
                optional: _a_opt,
            },
            AttrSet {
                field_keys: b_keys,
                open: b_open,
                optional: b_opt,
            },
        ) => {
            if !a_open {
                for field in b_keys.iter() {
                    if !a_keys.contains(field) && !b_opt.contains(field) {
                        return true;
                    }
                }
            }
            if !b_open {
                for field in a_keys.iter() {
                    if !b_keys.contains(field) && !_a_opt.contains(field) {
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
                field_keys: &[],
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

#[cfg(test)]
mod hegel_tests {
    use super::*;
    use crate::hegel_gen::{all_prims, ALL_PRIMS};
    use hegel::generators;
    use hegel::TestCase;

    /// Owned backing data for a `ConstructorShape`, which only borrows.
    #[derive(Debug, Clone)]
    enum Shape {
        Primitive(PrimitiveTy),
        AttrSet {
            keys: Vec<SmolStr>,
            open: bool,
            optional: BTreeSet<SmolStr>,
        },
        List,
        Lambda,
        Opaque,
    }

    impl Shape {
        fn view(&self) -> ConstructorShape<'_> {
            match self {
                Shape::Primitive(p) => ConstructorShape::Primitive(*p),
                Shape::AttrSet {
                    keys,
                    open,
                    optional,
                } => ConstructorShape::AttrSet {
                    field_keys: keys,
                    open: *open,
                    optional,
                },
                Shape::List => ConstructorShape::List,
                Shape::Lambda => ConstructorShape::Lambda,
                Shape::Opaque => ConstructorShape::Opaque,
            }
        }
    }

    const FIELD_NAMES: [&str; 5] = ["a", "b", "c", "__functor", "x"];

    #[hegel::composite]
    fn shapes(tc: &TestCase) -> Shape {
        match tc.draw(generators::integers::<u8>().max_value(4)) {
            0 => Shape::Primitive(tc.draw(all_prims())),
            1 => {
                let mut keys: Vec<SmolStr> = tc
                    .draw(
                        generators::vecs(generators::sampled_from(FIELD_NAMES.to_vec()))
                            .max_size(FIELD_NAMES.len())
                            .unique(true),
                    )
                    .into_iter()
                    .map(SmolStr::from)
                    .collect();
                keys.sort();
                let mut optional = BTreeSet::new();
                for k in &keys {
                    if tc.draw(generators::booleans()) {
                        optional.insert(k.clone());
                    }
                }
                Shape::AttrSet {
                    keys,
                    open: tc.draw(generators::booleans()),
                    optional,
                }
            }
            2 => Shape::List,
            3 => Shape::Lambda,
            _ => Shape::Opaque,
        }
    }

    #[hegel::test]
    fn disjoint_symmetric(tc: TestCase) {
        let a = tc.draw(shapes());
        let b = tc.draw(shapes());
        assert_eq!(
            are_shapes_disjoint(&a.view(), &b.view()),
            are_shapes_disjoint(&b.view(), &a.view())
        );
    }

    #[hegel::test]
    fn disjoint_irreflexive(tc: TestCase) {
        let a = tc.draw(shapes());
        assert!(!are_shapes_disjoint(&a.view(), &a.view()));
    }

    #[hegel::test]
    fn opaque_never_disjoint(tc: TestCase) {
        let a = tc.draw(shapes());
        assert!(!are_shapes_disjoint(&a.view(), &ConstructorShape::Opaque));
    }

    #[hegel::test]
    fn subtype_primitives_overlap(tc: TestCase) {
        // Construct related pairs directly: only a handful exist in the lattice.
        let related: Vec<(PrimitiveTy, PrimitiveTy)> = ALL_PRIMS
            .iter()
            .flat_map(|a| ALL_PRIMS.iter().map(move |b| (*a, *b)))
            .filter(|(a, b)| a.is_subtype_of(b) || b.is_subtype_of(a))
            .collect();
        let (a, b) = tc.draw(generators::sampled_from(related));
        assert!(!are_shapes_disjoint(
            &ConstructorShape::Primitive(a),
            &ConstructorShape::Primitive(b)
        ));
    }

    /// The primitive lattice: reflexive-by-exclusion, antisymmetric, transitive.
    #[hegel::test]
    fn primitive_subtype_is_strict_partial_order(tc: TestCase) {
        let a = tc.draw(all_prims());
        let b = tc.draw(all_prims());
        assert!(!a.is_subtype_of(&a));
        assert!(!(a.is_subtype_of(&b) && b.is_subtype_of(&a)));
        for c in ALL_PRIMS {
            if a.is_subtype_of(&b) && b.is_subtype_of(&c) {
                assert!(a.is_subtype_of(&c));
            }
        }
    }
}
