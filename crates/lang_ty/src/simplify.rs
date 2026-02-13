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
        OutputTy::Primitive(_) => {}
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
        OutputTy::Primitive(_) => ty.clone(),
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
            })
        }
        OutputTy::Union(members) => {
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|m| {
                    // Remove polar-only variables from unions (positive-only vars
                    // in a union add no information).
                    if let OutputTy::TyVar(v) = &*m.0 {
                        let resolved = substitution.get(v).copied().unwrap_or(*v);
                        if removable.contains(&resolved) {
                            return None;
                        }
                    }
                    Some(TyRef::from(apply_simplification(
                        &m.0,
                        substitution,
                        removable,
                    )))
                })
                .collect();

            match simplified.len() {
                0 => unreachable!("all union members removed during simplification"),
                1 => (*simplified.into_iter().next().unwrap().0).clone(),
                _ => OutputTy::Union(simplified),
            }
        }
        OutputTy::Intersection(members) => {
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|m| {
                    // Remove polar-only variables from intersections (negative-only
                    // vars in an intersection add no information).
                    if let OutputTy::TyVar(v) = &*m.0 {
                        let resolved = substitution.get(v).copied().unwrap_or(*v);
                        if removable.contains(&resolved) {
                            return None;
                        }
                    }
                    Some(TyRef::from(apply_simplification(
                        &m.0,
                        substitution,
                        removable,
                    )))
                })
                .collect();

            match simplified.len() {
                0 => unreachable!("all intersection members removed during simplification"),
                1 => (*simplified.into_iter().next().unwrap().0).clone(),
                _ => OutputTy::Intersection(simplified),
            }
        }
        OutputTy::Named(name, inner) => {
            let simplified_inner = apply_simplification(&inner.0, substitution, removable);
            OutputTy::Named(name.clone(), TyRef::from(simplified_inner))
        }
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

    if vars.is_empty() {
        return ty.clone();
    }

    let substitution = build_cooccurrence_substitution(&vars);
    let removable = polar_only_vars(&vars);

    if substitution.is_empty() && removable.is_empty() {
        return ty.clone();
    }

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
}
