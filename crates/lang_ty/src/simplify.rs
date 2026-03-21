// ==============================================================================
// Co-occurrence Simplification (SimpleSub §4.2)
// ==============================================================================
//
// Simplifies canonicalized OutputTy by:
// 1. Polarity analysis — track which polarities each variable appears in
// 2. Co-occurrence grouping — merge variables that always appear together
// 3. Apply and collapse — substitute merged vars, remove polar-only vars

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::arena::TyRef;
use crate::{OutputTy, TypeArena};

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

#[derive(Debug)]
struct VarInfo {
    polarity: Polarity,
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
    arena: &TypeArena,
    ty: TyRef,
    positive: bool,
    path: &mut Vec<PathSegment>,
    vars: &mut FxHashMap<u32, VarInfo>,
) {
    stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
        let pol = if positive {
            Polarity::Positive
        } else {
            Polarity::Negative
        };

        match &arena[ty] {
            OutputTy::TyVar(v) => {
                let v = *v;
                let type_path = TypePath(path.clone());
                vars.entry(v)
                    .and_modify(|info| {
                        info.polarity = info.polarity.merge(pol);
                        info.occurrences.insert(type_path.clone());
                    })
                    .or_insert_with(|| VarInfo::new(pol, type_path));
            }
            OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top | OutputTy::Extern(_) => {}
            OutputTy::List(inner) => {
                let inner = *inner;
                path.push(PathSegment::ListElem);
                analyze(arena, inner, positive, path, vars);
                path.pop();
            }
            OutputTy::Lambda { param, body } => {
                let (param, body) = (*param, *body);
                path.push(PathSegment::LambdaParam);
                analyze(arena, param, !positive, path, vars);
                path.pop();

                path.push(PathSegment::LambdaBody);
                analyze(arena, body, positive, path, vars);
                path.pop();
            }
            OutputTy::AttrSet(attr) => {
                let fields: Vec<_> = attr.fields.iter().map(|(k, &v)| (k.clone(), v)).collect();
                let dyn_ty = attr.dyn_ty;
                for (k, v) in fields {
                    path.push(PathSegment::AttrField(k));
                    analyze(arena, v, positive, path, vars);
                    path.pop();
                }
                if let Some(dyn_ty) = dyn_ty {
                    path.push(PathSegment::AttrDyn);
                    analyze(arena, dyn_ty, positive, path, vars);
                    path.pop();
                }
            }
            OutputTy::Union(members) => {
                let members: Vec<_> = members.clone();
                for (i, m) in members.iter().enumerate() {
                    path.push(PathSegment::UnionMember(i));
                    analyze(arena, *m, positive, path, vars);
                    path.pop();
                }
            }
            OutputTy::Intersection(members) => {
                let members: Vec<_> = members.clone();
                for (i, m) in members.iter().enumerate() {
                    path.push(PathSegment::IntersectionMember(i));
                    analyze(arena, *m, positive, path, vars);
                    path.pop();
                }
            }
            OutputTy::Named(_, inner) => {
                let inner = *inner;
                analyze(arena, inner, positive, path, vars);
            }
            OutputTy::Neg(inner) => {
                let inner = *inner;
                analyze(arena, inner, !positive, path, vars);
            }
        }
    });
}

// ==============================================================================
// Co-occurrence grouping
// ==============================================================================

fn build_cooccurrence_substitution(vars: &FxHashMap<u32, VarInfo>) -> FxHashMap<u32, u32> {
    let mut groups: FxHashMap<&BTreeSet<TypePath>, Vec<u32>> = FxHashMap::default();
    for (&var, info) in vars {
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

fn polar_only_vars(vars: &FxHashMap<u32, VarInfo>) -> FxHashSet<u32> {
    vars.iter()
        .filter(|(_, info)| info.polarity != Polarity::Both)
        .map(|(&var, _)| var)
        .collect()
}

fn is_removable_var_member(
    arena: &TypeArena,
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
            if let OutputTy::TyVar(v) = &arena[*inner] {
                let resolved = substitution.get(v).copied().unwrap_or(*v);
                removable.contains(&resolved)
            } else {
                false
            }
        }
        _ => false,
    }
}

fn apply_simplification(
    arena: &mut TypeArena,
    ty: TyRef,
    substitution: &FxHashMap<u32, u32>,
    removable: &FxHashSet<u32>,
) -> TyRef {
    let node = arena[ty].clone();
    stacker::maybe_grow(256 * 1024, 1024 * 1024, || match &node {
        OutputTy::TyVar(v) => {
            let resolved = substitution.get(v).copied().unwrap_or(*v);
            arena.intern(OutputTy::TyVar(resolved))
        }
        OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top | OutputTy::Extern(_) => ty,
        OutputTy::List(inner) => {
            let new_inner = apply_simplification(arena, *inner, substitution, removable);
            arena.intern(OutputTy::List(new_inner))
        }
        OutputTy::Lambda { param, body } => {
            let new_param = apply_simplification(arena, *param, substitution, removable);
            let new_body = apply_simplification(arena, *body, substitution, removable);
            arena.intern(OutputTy::Lambda {
                param: new_param,
                body: new_body,
            })
        }
        OutputTy::AttrSet(attr) => {
            let fields: Vec<_> = attr.fields.iter().map(|(k, &v)| (k.clone(), v)).collect();
            let dyn_ty = attr.dyn_ty;
            let optional_fields = attr.optional_fields.clone();
            let open = attr.open;

            let new_fields = fields
                .into_iter()
                .map(|(k, v)| (k, apply_simplification(arena, v, substitution, removable)))
                .collect();
            let new_dyn_ty =
                dyn_ty.map(|d| apply_simplification(arena, d, substitution, removable));
            arena.intern(OutputTy::AttrSet(crate::AttrSetTy {
                fields: new_fields,
                dyn_ty: new_dyn_ty,
                open,
                optional_fields,
            }))
        }
        OutputTy::Union(members) => {
            let members = members.clone();
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|&m| {
                    let m_node = arena[m].clone();
                    if is_removable_var_member(arena, &m_node, substitution, removable) {
                        return None;
                    }
                    let s = apply_simplification(arena, m, substitution, removable);
                    let s_node = arena[s].clone();
                    if matches!(s_node, OutputTy::Bottom) {
                        return None;
                    }
                    if matches!(s_node, OutputTy::Top) {
                        return Some(arena.intern(OutputTy::Top));
                    }
                    Some(s)
                })
                .collect();

            if simplified
                .iter()
                .any(|&m| matches!(arena[m], OutputTy::Top))
            {
                return arena.intern(OutputTy::Top);
            }

            // Flatten nested unions
            let mut flat = Vec::with_capacity(simplified.len());
            for m in &simplified {
                if let OutputTy::Union(inner) = arena[*m].clone() {
                    flat.extend(inner);
                } else {
                    flat.push(*m);
                }
            }
            flat.dedup();

            match flat.len() {
                0 => apply_simplification(arena, members[0], substitution, &FxHashSet::default()),
                1 => flat[0],
                _ => arena.intern(OutputTy::Union(flat)),
            }
        }
        OutputTy::Intersection(members) => {
            let members = members.clone();
            let simplified: Vec<TyRef> = members
                .iter()
                .filter_map(|&m| {
                    let m_node = arena[m].clone();
                    if is_removable_var_member(arena, &m_node, substitution, removable) {
                        return None;
                    }
                    let s = apply_simplification(arena, m, substitution, removable);
                    let s_node = arena[s].clone();
                    if matches!(s_node, OutputTy::Top) {
                        return None;
                    }
                    Some(s)
                })
                .collect();

            if simplified
                .iter()
                .any(|&m| matches!(arena[m], OutputTy::Bottom))
            {
                return arena.intern(OutputTy::Bottom);
            }

            // Flatten nested intersections
            let mut flat = Vec::with_capacity(simplified.len());
            for m in &simplified {
                if let OutputTy::Intersection(inner) = arena[*m].clone() {
                    flat.extend(inner);
                } else {
                    flat.push(*m);
                }
            }
            flat.dedup();

            match flat.len() {
                0 => apply_simplification(arena, members[0], substitution, &FxHashSet::default()),
                1 => flat[0],
                _ => arena.intern(OutputTy::Intersection(flat)),
            }
        }
        OutputTy::Named(name, inner) => {
            let name = name.clone();
            let new_inner = apply_simplification(arena, *inner, substitution, removable);
            arena.intern(OutputTy::Named(name, new_inner))
        }
        OutputTy::Neg(inner) => {
            let new_inner = apply_simplification(arena, *inner, substitution, removable);
            arena.intern(OutputTy::Neg(new_inner))
        }
    })
}

// ==============================================================================
// Public API
// ==============================================================================

/// Simplify a type using co-occurrence analysis. Takes a mutable arena
/// because simplification may intern new type nodes.
pub fn simplify(arena: &mut TypeArena, ty: TyRef) -> TyRef {
    let mut result = simplify_once(arena, ty);
    for _ in 0..5 {
        let next = simplify_once(arena, result);
        if next == result {
            break;
        }
        result = next;
    }
    result
}

fn simplify_once(arena: &mut TypeArena, ty: TyRef) -> TyRef {
    let mut vars = FxHashMap::default();
    let mut path = Vec::new();
    analyze(arena, ty, true, &mut path, &mut vars);

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

    apply_simplification(arena, ty, &substitution, &removable)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arc_ty;

    #[test]
    fn simplify_identity_fn() {
        let mut arena = TypeArena::new();
        let ty = arc_ty!(&mut arena, (# 0) -> (# 0));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_removes_positive_only_var_from_union() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let var_ref = arena.intern(OutputTy::TyVar(42));
        let ty = arena.intern(OutputTy::Union(vec![int_ref, var_ref]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, int_ref);
    }

    #[test]
    fn simplify_does_not_merge_different_occurrences() {
        let mut arena = TypeArena::new();
        let ty = arc_ty!(&mut arena, ((# 0) -> (# 1)) -> ((# 0) -> (# 1)));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_all_intersection_members_removable() {
        let mut arena = TypeArena::new();
        let v10 = arena.intern(OutputTy::TyVar(10));
        let v11 = arena.intern(OutputTy::TyVar(11));
        let ty = arena.intern(OutputTy::Intersection(vec![v10, v11]));
        let result = simplify(&mut arena, ty);
        assert_eq!(arena[result], OutputTy::TyVar(10));
    }

    #[test]
    fn simplify_all_union_members_removable() {
        let mut arena = TypeArena::new();
        let v20 = arena.intern(OutputTy::TyVar(20));
        let v21 = arena.intern(OutputTy::TyVar(21));
        let ty = arena.intern(OutputTy::Union(vec![v20, v21]));
        let result = simplify(&mut arena, ty);
        assert_eq!(arena[result], OutputTy::TyVar(20));
    }

    #[test]
    fn simplify_preserves_different_occurrence_vars() {
        let mut arena = TypeArena::new();
        let ty = arc_ty!(&mut arena, (# 0) -> (# 1));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_neg_flips_polarity_in_union() {
        let mut arena = TypeArena::new();
        let neg_var = arc_ty!(&mut arena, neg!(# 5));
        let int_ref = arc_ty!(&mut arena, Int);
        let ty = arena.intern(OutputTy::Union(vec![neg_var, int_ref]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, int_ref);
    }

    #[test]
    fn simplify_neg_both_polarities_preserved() {
        let mut arena = TypeArena::new();
        let v3 = arena.intern(OutputTy::TyVar(3));
        let neg_v3 = arena.intern(OutputTy::Neg(v3));
        let ty = arena.intern(OutputTy::Intersection(vec![v3, neg_v3]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_neg_in_intersection_removed() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let neg_var = arc_ty!(&mut arena, neg!(# 7));
        let ty = arena.intern(OutputTy::Intersection(vec![int_ref, neg_var]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, int_ref);
    }

    #[test]
    fn simplify_neg_preserves_concrete() {
        let mut arena = TypeArena::new();
        let ty = arc_ty!(&mut arena, neg!(Null));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, ty);
    }

    #[test]
    fn simplify_top_absorbing_for_union() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let top_ref = arc_ty!(&mut arena, Top);
        let ty = arena.intern(OutputTy::Union(vec![int_ref, top_ref]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, top_ref);
    }

    #[test]
    fn simplify_top_identity_for_intersection() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let top_ref = arc_ty!(&mut arena, Top);
        let ty = arena.intern(OutputTy::Intersection(vec![int_ref, top_ref]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, int_ref);
    }

    #[test]
    fn simplify_top_alone_in_intersection() {
        let mut arena = TypeArena::new();
        let top_ref = arc_ty!(&mut arena, Top);
        let v42 = arena.intern(OutputTy::TyVar(42));
        let ty = arena.intern(OutputTy::Intersection(vec![top_ref, v42]));
        let result = simplify(&mut arena, ty);
        assert_eq!(result, top_ref);
    }

    // TODO: PBT for simplify idempotency needs arena-aware Arbitrary impl
}
