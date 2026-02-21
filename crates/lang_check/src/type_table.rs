// ==============================================================================
// TypeTable — storage layer for type allocation, caching, and resolution
// ==============================================================================
//
// Isolates the core type storage operations (allocation, deduplication,
// concrete-type resolution) from the inference orchestration in CheckCtx.
// constrain() and its recursive helpers stay on CheckCtx because they
// interleave storage operations with current_expr tracking.

use std::collections::{HashMap, HashSet};

use super::TyId;
use crate::storage::{TypeEntry, TypeStorage, TypeVariable};
use lang_ty::{PrimitiveTy, Ty};

#[derive(Debug, Clone)]
pub(crate) struct TypeTable {
    pub(crate) storage: TypeStorage,

    /// Cache (sub, sup) pairs already processed by constrain() to avoid cycles.
    /// Intentionally never cleared between SCC groups: extrusion creates fresh
    /// vars linked to old ones via constrain(), and re-processing those pairs
    /// would cause infinite loops across extrusion boundaries. The cache is
    /// scoped to the lifetime of the owning CheckCtx (one per file), so it
    /// doesn't grow across files.
    pub(crate) constrain_cache: HashSet<(TyId, TyId)>,

    /// Primitive type cache for deduplication.
    pub(crate) prim_cache: HashMap<PrimitiveTy, TyId>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            storage: TypeStorage::new(),
            constrain_cache: HashSet::new(),
            prim_cache: HashMap::new(),
        }
    }

    /// Allocate a fresh type variable at the current level.
    pub fn new_var(&mut self) -> TyId {
        self.storage.new_var()
    }

    /// Allocate a concrete type and return its TyId.
    ///
    /// Applies double negation elimination: `Neg(Neg(x))` → `x`, so double
    /// negations never exist in the type table during inference.
    pub fn alloc_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        if let Ty::Neg(inner) = &ty {
            if let TypeEntry::Concrete(Ty::Neg(x)) = self.storage.get(*inner) {
                return *x;
            }
        }
        self.storage.new_concrete(ty)
    }

    /// Allocate a primitive type, deduplicating via cache.
    pub fn alloc_prim(&mut self, prim: PrimitiveTy) -> TyId {
        if let Some(&id) = self.prim_cache.get(&prim) {
            return id;
        }
        let id = self.alloc_concrete(Ty::Primitive(prim));
        self.prim_cache.insert(prim, id);
        id
    }

    /// Walk lower bounds transitively to find a Concrete entry and return its
    /// TyId. Used to resolve partial-application result variables (which point
    /// to a Lambda via lower bounds) so poly_type_env stores the structural type
    /// that extrude can traverse.
    pub fn resolve_to_concrete_id(&self, ty_id: TyId) -> Option<TyId> {
        let mut visited = HashSet::new();
        self.resolve_to_concrete_id_inner(ty_id, &mut visited)
    }

    fn resolve_to_concrete_id_inner(
        &self,
        ty_id: TyId,
        visited: &mut HashSet<TyId>,
    ) -> Option<TyId> {
        if !visited.insert(ty_id) {
            return None; // Cycle detected.
        }
        match self.storage.get(ty_id) {
            TypeEntry::Concrete(_) => Some(ty_id),
            TypeEntry::Variable(v) => {
                let bounds = v.lower_bounds.clone();
                for lb in bounds {
                    if let Some(id) = self.resolve_to_concrete_id_inner(lb, visited) {
                        return Some(id);
                    }
                }
                None
            }
        }
    }

    /// Walk lower bounds of a variable to find a concrete type, if one exists.
    /// Delegates to `resolve_to_concrete_id` to avoid duplicating the traversal
    /// and cycle-detection logic.
    pub fn find_concrete(&self, ty_id: TyId) -> Option<Ty<TyId>> {
        let concrete_id = self.resolve_to_concrete_id(ty_id)?;
        match self.storage.get(concrete_id) {
            TypeEntry::Concrete(ty) => Some(ty.clone()),
            _ => None,
        }
    }

    /// Check if a variable has been pinned to a simple concrete type — i.e. the
    /// same primitive type appears as both a direct lower and upper bound. This
    /// indicates the variable was fully resolved (e.g. by overload resolution) and
    /// is no longer truly polymorphic.
    ///
    /// Only primitives are considered "pinned" — types with internal structure
    /// (Lambda, List, AttrSet) may contain polymorphic sub-components that need
    /// proper extrusion.
    pub fn find_pinned_concrete(&self, v: &TypeVariable) -> Option<Ty<TyId>> {
        // Collect primitive types from direct lower bounds.
        let lower_prims: Vec<_> = v
            .lower_bounds
            .iter()
            .filter_map(|&lb| {
                if let TypeEntry::Concrete(ty @ Ty::Primitive(_)) = self.storage.get(lb) {
                    Some(ty.clone())
                } else {
                    None
                }
            })
            .collect();

        // Check if any of those also appear as a direct upper bound.
        for &ub in &v.upper_bounds {
            if let TypeEntry::Concrete(ub_ty @ Ty::Primitive(_)) = self.storage.get(ub) {
                if lower_prims.contains(ub_ty) {
                    return Some(ub_ty.clone());
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_ty::PrimitiveTy;

    #[test]
    fn new_var_allocates_incrementing_ids() {
        let mut tt = TypeTable::new();
        let v0 = tt.new_var();
        let v1 = tt.new_var();
        let v2 = tt.new_var();
        assert_eq!(v0, TyId::from(0u32));
        assert_eq!(v1, TyId::from(1u32));
        assert_eq!(v2, TyId::from(2u32));
    }

    #[test]
    fn alloc_concrete_double_negation_elimination() {
        let mut tt = TypeTable::new();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);

        // Neg(int) — normal allocation.
        let neg_int = tt.alloc_concrete(Ty::Neg(int_ty));
        assert!(matches!(
            tt.storage.get(neg_int),
            TypeEntry::Concrete(Ty::Neg(_))
        ));

        // Neg(Neg(int)) — should return the original int TyId.
        let neg_neg_int = tt.alloc_concrete(Ty::Neg(neg_int));
        assert_eq!(neg_neg_int, int_ty);
    }

    #[test]
    fn alloc_prim_deduplicates() {
        let mut tt = TypeTable::new();
        let int1 = tt.alloc_prim(PrimitiveTy::Int);
        let int2 = tt.alloc_prim(PrimitiveTy::Int);
        assert_eq!(int1, int2, "repeated alloc_prim should return same TyId");

        let string = tt.alloc_prim(PrimitiveTy::String);
        assert_ne!(
            int1, string,
            "different primitives should get different TyIds"
        );
    }

    #[test]
    fn resolve_to_concrete_id_follows_lower_bounds() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let param = tt.alloc_prim(PrimitiveTy::Int);
        let body = tt.alloc_prim(PrimitiveTy::String);
        let lambda = tt.alloc_concrete(Ty::Lambda { param, body });

        // var has lambda as a lower bound.
        tt.storage.add_lower_bound(var, lambda);

        let resolved = tt.resolve_to_concrete_id(var);
        assert_eq!(resolved, Some(lambda));
    }

    #[test]
    fn resolve_to_concrete_id_handles_cycles() {
        let mut tt = TypeTable::new();
        let v1 = tt.new_var();
        let v2 = tt.new_var();

        // Create a cycle: v1 → v2 → v1.
        tt.storage.add_lower_bound(v1, v2);
        tt.storage.add_lower_bound(v2, v1);

        // Should return None rather than looping.
        assert_eq!(tt.resolve_to_concrete_id(v1), None);
    }

    #[test]
    fn find_pinned_concrete_detects_pinned_var() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);

        // Pin the variable: int appears as both lower and upper bound.
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, int_ty);

        let v = tt.storage.get_var(var).unwrap().clone();
        assert_eq!(
            tt.find_pinned_concrete(&v),
            Some(Ty::Primitive(PrimitiveTy::Int))
        );
    }

    #[test]
    fn find_pinned_concrete_returns_none_for_unpinned() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let string_ty = tt.alloc_prim(PrimitiveTy::String);

        // Only int as lower bound, only string as upper — not pinned.
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, string_ty);

        let v = tt.storage.get_var(var).unwrap().clone();
        assert_eq!(tt.find_pinned_concrete(&v), None);
    }
}
