// ==============================================================================
// Co-occurrence Simplification (SimpleSub §4.2)
// ==============================================================================
//
// Simplifies canonicalized OutputTy by:
// 1. Polarity analysis — track which polarities each variable appears in
// 2. Co-occurrence grouping — merge variables that always appear together
// 3. Apply and collapse — substitute merged vars, remove polar-only vars
//
// A variable that only appears in positive position (output/union) or only in
// negative position (input/intersection) adds no information — it's unbounded
// in the other direction and can be removed. Variables with identical occurrence
// patterns can be merged into a single representative.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{AttrSetTy, OutputTy, TyRef};

// ==============================================================================
// Polarity tracking
// ==============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
    Both,
}

impl Polarity {
    fn merge(self, other: Polarity) -> Polarity {
        if self == other {
            self
        } else {
            Polarity::Both
        }
    }
}

/// A path through the type tree, used to identify co-occurring variables.
/// Two variables co-occur if they appear at exactly the same set of paths.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TypePath(Vec<PathSegment>);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PathSegment {
    LambdaParam,
    LambdaBody,
    ListElem,
    AttrField(smol_str::SmolStr),
    AttrDyn,
    UnionMember(usize),
    IntersectionMember(usize),
}

/// Information gathered about each type variable during analysis.
#[derive(Debug)]
struct VarInfo {
    polarity: Polarity,
    /// Set of paths where this variable appears.
    occurrences: BTreeSet<TypePath>,
}

impl VarInfo {
    fn new(polarity: Polarity, path: TypePath) -> Self {
        let mut occurrences = BTreeSet::new();
        occurrences.insert(path);
        Self {
            polarity,
            occurrences,
        }
    }
}

// ==============================================================================
// Analysis pass
// ==============================================================================

fn analyze(
    ty: &OutputTy,
    positive: bool,
    path: &mut Vec<PathSegment>,
    vars: &mut FxHashMap<u32, VarInfo>,
) {
    let pol = if positive {
        Polarity::Positive
    } else {
        Polarity::Negative
    };

    match ty {
        OutputTy::TyVar(v) => {
            let type_path = TypePath(path.clone());
            vars.entry(*v)
                .and_modify(|info| {
                    info.polarity = info.polarity.merge(pol);
                    info.occurrences.insert(type_path.clone());
                })
                .or_insert_with(|| VarInfo::new(pol, type_path));
        }
        OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {}
        OutputTy::List(inner) => {
            path.push(PathSegment::ListElem);
            analyze(&inner.0, positive, path, vars);
            path.pop();
        }
        OutputTy::Lambda { param, body } => {
            path.push(PathSegment::LambdaParam);
            analyze(&param.0, !positive, path, vars);
            path.pop();

            path.push(PathSegment::LambdaBody);
            analyze(&body.0, positive, path, vars);
            path.pop();
        }
        OutputTy::AttrSet(attr) => {
            for (k, v) in &attr.fields {
                path.push(PathSegment::AttrField(k.clone()));
                analyze(&v.0, positive, path, vars);
                path.pop();
            }
            if let Some(dyn_ty) = &attr.dyn_ty {
                path.push(PathSegment::AttrDyn);
                analyze(&dyn_ty.0, positive, path, vars);
                path.pop();
            }
        }
        OutputTy::Union(members) => {
            for (i, m) in members.iter().enumerate() {
                path.push(PathSegment::UnionMember(i));
                analyze(&m.0, positive, path, vars);
                path.pop();
            }
        }
        OutputTy::Intersection(members) => {
            for (i, m) in members.iter().enumerate() {
                path.push(PathSegment::IntersectionMember(i));
                analyze(&m.0, positive, path, vars);
                path.pop();
            }
        }
        OutputTy::Named(_, inner) => {
            analyze(&inner.0, positive, path, vars);
        }
        // Negation flips polarity, like Lambda param.
        OutputTy::Neg(inner) => {
            analyze(&inner.0, !positive, path, vars);
        }
    }
}

// ==============================================================================
// Co-occurrence grouping
// ==============================================================================

/// Build a substitution map that merges variables with identical occurrence sets.
/// The representative (lowest-numbered var in the group) is kept.
fn build_cooccurrence_substitution(vars: &FxHashMap<u32, VarInfo>) -> FxHashMap<u32, u32> {
    // Group variables by their occurrence set.
    let mut groups: FxHashMap<&BTreeSet<TypePath>, Vec<u32>> = FxHashMap::default();
    for (&var, info) in vars {
        // Only merge variables that appear in both polarities — polar-only
        // variables will be removed entirely.
        if info.polarity == Polarity::Both {
            groups.entry(&info.occurrences).or_default().push(var);
        }
    }

    let mut substitution = FxHashMap::default();
    for (_occ, mut group) in groups {
        if group.len() <= 1 {
            continue;
        }
        group.sort();
        let representative = group[0];
        for &var in &group[1..] {
            substitution.insert(var, representative);
        }
    }
    substitution
}

// ==============================================================================
// Apply substitution and collapse
// ==============================================================================

/// Determine which variables should be removed (polar-only).
fn polar_only_vars(vars: &FxHashMap<u32, VarInfo>) -> FxHashSet<u32> {
    vars.iter()
        .filter(|(_, info)| info.polarity != Polarity::Both)
        .map(|(&var, _)| var)
        .collect()
}

/// Check if a union/intersection member is a removable variable reference:
/// either a bare `TyVar(v)` or `Neg(TyVar(v))` where `v` (after substitution)
/// is in the removable set. `Neg(TyVar(v))` with a polar-only `v` carries no
/// more information than the bare variable — both are unconstrained in one
/// direction.
fn is_removable_var_member(
    ty: &OutputTy,
    substitution: &FxHashMap<u32, u32>,
    removable: &FxHashSet<u32>,
) -> bool {
    match ty {
        OutputTy::TyVar(v) => {
            let resolved = substitution.get(v).copied().unwrap_or(*v);
            removable.contains(&resolved)
        }
        OutputTy::Neg(inner) => {
            if let OutputTy::TyVar(v) = &*inner.0 {
                let resolved = substitution.get(v).copied().unwrap_or(*v);
                removable.contains(&resolved)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Apply the substitution + removal to produce a simplified type.
fn apply_simplification(
    ty: &OutputTy,
    substitution: &FxHashMap<u32, u32>,
    removable: &FxHashSet<u32>,
) -> OutputTy {
    match ty {
        OutputTy::TyVar(v) => {
            let resolved = substitution.get(v).copied().unwrap_or(*v);
            OutputTy::TyVar(resolved)
        }
        OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => ty.clone(),
        OutputTy::List(inner) => OutputTy::List(TyRef::from(apply_simplification(
            &inner.0,
            substitution,
            removable,
        ))),
        OutputTy::Lambda { param, body } => OutputTy::Lambda {
            param: TyRef::from(apply_simplification(&param.0, substitution, removable)),
            body: TyRef::from(apply_simplification(&body.0, substitution, removable)),
        },
        OutputTy::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        TyRef::from(apply_simplification(&v.0, substitution, removable)),
                    )
                })
                .collect();
            let dyn_ty = attr
                .dyn_ty
                .as_ref()
                .map(|d| TyRef::from(apply_simplification(&d.0, substitution, removable)));
            OutputTy::AttrSet(AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }
        OutputTy::Union(members) => {
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|m| {
                    // Remove polar-only variables from unions (positive-only vars
                    // in a union add no information). Also handles Neg(TyVar(v))
                    // where v is removable — the negation of an uninformative
                    // variable is itself uninformative.
                    if is_removable_var_member(&m.0, substitution, removable) {
                        return None;
                    }
                    let s = apply_simplification(&m.0, substitution, removable);
                    // Bottom is the identity for union: A ∨ ⊥ = A.
                    if matches!(s, OutputTy::Bottom) {
                        return None;
                    }
                    // Top is absorbing for union: A ∨ ⊤ = ⊤.
                    if matches!(s, OutputTy::Top) {
                        return Some(TyRef::from(OutputTy::Top));
                    }
                    Some(TyRef::from(s))
                })
                .collect();

            // Top is absorbing for union: if any member is Top, whole union is Top.
            if simplified.iter().any(|m| matches!(&*m.0, OutputTy::Top)) {
                return OutputTy::Top;
            }

            match simplified.len() {
                // All members were polar-only type variables. Keep the first
                // member (after substitution) as a representative — it's
                // unconstrained and effectively represents ⊥ in this position.
                0 => apply_simplification(&members[0].0, substitution, &FxHashSet::default()),
                1 => (*simplified.into_iter().next().unwrap().0).clone(),
                _ => OutputTy::Union(simplified),
            }
        }
        OutputTy::Intersection(members) => {
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|m| {
                    // Remove polar-only variables from intersections (negative-only
                    // vars in an intersection add no information). Also handles
                    // Neg(TyVar(v)) where v is removable.
                    if is_removable_var_member(&m.0, substitution, removable) {
                        return None;
                    }
                    let s = apply_simplification(&m.0, substitution, removable);
                    // Top is the identity for intersection: A ∧ ⊤ = A.
                    if matches!(s, OutputTy::Top) {
                        return None;
                    }
                    Some(TyRef::from(s))
                })
                .collect();

            // Bottom is absorbing for intersection: A ∧ ⊥ = ⊥.
            if simplified.iter().any(|m| matches!(&*m.0, OutputTy::Bottom)) {
                return OutputTy::Bottom;
            }

            match simplified.len() {
                // All members were polar-only type variables. Keep the first
                // member (after substitution) as a representative — it's
                // unconstrained and effectively represents ⊤ in this position.
                0 => apply_simplification(&members[0].0, substitution, &FxHashSet::default()),
                1 => (*simplified.into_iter().next().unwrap().0).clone(),
                _ => OutputTy::Intersection(simplified),
            }
        }
        OutputTy::Named(name, inner) => {
            let simplified_inner = apply_simplification(&inner.0, substitution, removable);
            OutputTy::Named(name.clone(), TyRef::from(simplified_inner))
        }
        OutputTy::Neg(inner) => OutputTy::Neg(TyRef::from(apply_simplification(
            &inner.0,
            substitution,
            removable,
        ))),
    }
}

// ==============================================================================
// Public API
// ==============================================================================

/// Simplify an OutputTy using co-occurrence analysis.
///
/// This removes type variables that appear in only one polarity (they're
/// unconstrained in the other direction) and merges variables that always
/// co-occur at the same positions.
pub fn simplify(ty: &OutputTy) -> OutputTy {
    let mut vars = FxHashMap::default();
    let mut path = Vec::new();
    analyze(ty, true, &mut path, &mut vars);

    let substitution = if vars.is_empty() {
        FxHashMap::default()
    } else {
        build_cooccurrence_substitution(&vars)
    };
    let removable = if vars.is_empty() {
        FxHashSet::default()
    } else {
        polar_only_vars(&vars)
    };

    // Always run apply_simplification — even without variable work to do,
    // it handles algebraic identities (Top in intersection, Top in union,
    // Bottom in union/intersection).
    apply_simplification(ty, &substitution, &removable)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arc_ty;

    #[test]
    fn simplify_identity_fn() {
        // (a -> a) should stay as (a -> a) — both polarities, single co-occurrence group
        let ty = arc_ty!((# 0) -> (# 0));
        let result = simplify(&ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_removes_positive_only_var_from_union() {
        // Union(int, a) where `a` only appears positively → just `int`
        let ty = OutputTy::Union(vec![
            TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Int)),
            TyRef::from(OutputTy::TyVar(42)),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::Primitive(crate::PrimitiveTy::Int));
    }

    #[test]
    fn simplify_does_not_merge_different_occurrences() {
        // (a -> b) -> (a -> b): a and b appear at different path sets,
        // so they should NOT be merged.
        let ty = arc_ty!(((# 0) -> (# 1)) -> ((# 0) -> (# 1)));
        let result = simplify(&ty);
        assert_eq!(result, ty);
    }

    #[test]
    #[ignore = "co-occurrence merging is rare in practice; polar-only removal is the main simplification"]
    fn simplify_merges_cooccurring_vars() {
        // { foo: (a, b), bar: (a, b) } encoded as attrset where a and b
        // appear at the exact same set of paths.
        // Simpler case using lambdas: a function that takes a pair of (a, b)
        // and returns a pair of (a, b). But since we don't have tuples,
        // use: a -> b -> { x: a, y: b } paired with a -> b -> { x: a, y: b }.
        //
        // Even simpler: in a union like Union(a, b), if both a and b appear
        // ONLY in that union, they co-occur trivially. But for the simplify
        // function, polar-only removal would eliminate them first.
        //
        // The most direct co-occurrence case: two attrset fields mapping to
        // the same pair of vars.
        // { x: a -> b, y: a -> b } — both a,b appear at same paths relative
        // to x and y. But paths include the field name, so they differ.
        //
        // Co-occurrence only helps when the EXACT SAME set of paths is shared.
        // This is rare in practice — the main value of simplify is
        // polar-only variable removal. Skip merge test for now.
    }

    #[test]
    fn simplify_all_intersection_members_removable() {
        // Intersection(a, b) where both vars are negative-only (appear only in
        // an intersection at top level). All members would be filtered out —
        // this must not panic. Regression test for the crash in nixpkgs.
        let ty = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::TyVar(10)),
            TyRef::from(OutputTy::TyVar(11)),
        ]);
        let result = simplify(&ty);
        // Should keep one representative variable rather than crashing.
        assert_eq!(result, OutputTy::TyVar(10));
    }

    #[test]
    fn simplify_all_union_members_removable() {
        // Union(a, b) where both vars are positive-only. Same scenario as
        // above but for unions.
        let ty = OutputTy::Union(vec![
            TyRef::from(OutputTy::TyVar(20)),
            TyRef::from(OutputTy::TyVar(21)),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::TyVar(20));
    }

    #[test]
    fn simplify_preserves_different_occurrence_vars() {
        // (a -> b) — a in negative, b in positive, both single-polarity → removed
        // But for a lambda, that means (⊤ -> ⊥) which is degenerate.
        // In practice this case represents an unconstrained function.
        // The simplification keeps the vars since they'd collapse otherwise.
        let ty = arc_ty!((# 0) -> (# 1));
        let result = simplify(&ty);
        // a is negative-only, b is positive-only — both get removed
        // But they're not in unions/intersections, so TyVar removal only
        // applies to union/intersection members. The vars remain.
        assert_eq!(result, ty);
    }

    // ======================================================================
    // Negation type simplification
    // ======================================================================
    //
    // Neg flips polarity (like lambda params). These tests verify that
    // polarity analysis through Neg correctly identifies removable
    // variables in unions and intersections.

    #[test]
    fn simplify_neg_flips_polarity_in_union() {
        // Union(Neg(TyVar(5)), Int) — polarity analysis correctly tracks
        // TyVar(5) as negative-only (through Neg). Since TyVar(5) is
        // single-polarity (removable), Neg(TyVar(5)) is also removed,
        // leaving just Int.
        let ty = OutputTy::Union(vec![
            TyRef::from(OutputTy::Neg(TyRef::from(OutputTy::TyVar(5)))),
            TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Int)),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::Primitive(crate::PrimitiveTy::Int));
    }

    #[test]
    fn simplify_neg_both_polarities_preserved() {
        // Intersection(TyVar(3), Neg(TyVar(3))) — TyVar(3) appears in
        // positive polarity (bare intersection member) and negative polarity
        // (inside Neg). Both polarities → NOT removable.
        let ty = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::TyVar(3)),
            TyRef::from(OutputTy::Neg(TyRef::from(OutputTy::TyVar(3)))),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_neg_in_intersection_removed() {
        // Intersection(Int, Neg(TyVar(7))) — TyVar(7) is single-polarity
        // (negative, through Neg in an intersection). Since it's removable,
        // the Neg(TyVar(7)) member is stripped, leaving just Int.
        let ty = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Int)),
            TyRef::from(OutputTy::Neg(TyRef::from(OutputTy::TyVar(7)))),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::Primitive(crate::PrimitiveTy::Int));
    }

    #[test]
    fn simplify_neg_preserves_concrete() {
        // Neg(Null) — no type variables, nothing to simplify.
        let ty = OutputTy::Neg(TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Null)));
        let result = simplify(&ty);
        assert_eq!(result, ty);
    }

    // ======================================================================
    // Top type simplification
    // ======================================================================

    #[test]
    fn simplify_top_absorbing_for_union() {
        // Union(Int, Top) → Top. Top absorbs all union members.
        let ty = OutputTy::Union(vec![
            TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Int)),
            TyRef::from(OutputTy::Top),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::Top);
    }

    #[test]
    fn simplify_top_identity_for_intersection() {
        // Intersection(Int, Top) → Int. Top is identity for intersection.
        let ty = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::Primitive(crate::PrimitiveTy::Int)),
            TyRef::from(OutputTy::Top),
        ]);
        let result = simplify(&ty);
        assert_eq!(result, OutputTy::Primitive(crate::PrimitiveTy::Int));
    }

    #[test]
    fn simplify_top_alone_in_intersection() {
        // Intersection(Top) → Top. When Top is the only member, return Top.
        // This shouldn't occur in practice (intersections have 2+ members),
        // but verify the algebra is correct.
        let ty = OutputTy::Intersection(vec![
            TyRef::from(OutputTy::Top),
            TyRef::from(OutputTy::TyVar(42)),
        ]);
        let result = simplify(&ty);
        // TyVar(42) is negative-only (in intersection at top level) → removed.
        // Top is also removed (identity). All members filtered → fallback.
        assert_eq!(result, OutputTy::Top);
    }

    proptest::proptest! {
        /// Simplification is idempotent: applying it twice yields the same
        /// result as applying it once.
        #[test]
        fn simplify_is_idempotent(ty: OutputTy) {
            let once = simplify(&ty);
            let twice = simplify(&once);
            proptest::prop_assert_eq!(once, twice);
        }
    }
}
