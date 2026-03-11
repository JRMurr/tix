// ==============================================================================
// TypeTable — storage layer for type allocation, caching, and resolution
// ==============================================================================
//
// Isolates the core type storage operations (allocation, deduplication,
// concrete-type resolution) from the inference orchestration in CheckCtx.
// constrain() and its recursive helpers stay on CheckCtx because they
// interleave storage operations with current_expr tracking.

use std::collections::HashSet;

use rustc_hash::{FxHashMap, FxHashSet};

use super::TyId;
use crate::storage::{TypeEntry, TypeStorage, TypeVariable};
use lang_ty::{PrimitiveTy, Ty};

/// Coarse type-constructor tag used to distinguish genuine unions from
/// compatible multi-bound variables. Two concrete types with the same head
/// (e.g. two `List(...)` with different elements) are structurally compatible
/// constraints, not a union. Different heads (e.g. `Primitive(Int)` vs
/// `Primitive(String)`) indicate a genuine union.
#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeHead {
    Primitive(PrimitiveTy),
    List,
    Lambda,
    AttrSet,
    Neg,
    Inter,
    Union,
    Named,
}

impl TypeHead {
    fn of(ty: &Ty<TyId>) -> Self {
        match ty {
            Ty::TyVar(_) => unreachable!("TyVar is not a concrete type"),
            Ty::Primitive(p) => TypeHead::Primitive(*p),
            Ty::List(_) => TypeHead::List,
            Ty::Lambda { .. } => TypeHead::Lambda,
            Ty::AttrSet(_) => TypeHead::AttrSet,
            Ty::Neg(_) => TypeHead::Neg,
            Ty::Inter(_, _) => TypeHead::Inter,
            Ty::Union(_, _) => TypeHead::Union,
            Ty::Named(_, _) => TypeHead::Named,
        }
    }
}

/// Storage layer for type allocation, caching, and resolution.
///
/// # Cache Invalidation Rules
///
/// All caches are scoped to the lifetime of a single `CheckCtx` (one per
/// file). None are cleared between SCC groups within a file. TypeStorage
/// is **mostly append-only** — entries are never removed, and concrete
/// entries are never mutated. The one exception is `replace_var_with_concrete`
/// used by bounds graph compaction, which overwrites a Variable slot with a
/// Concrete entry. Per-cache safety analysis:
///
/// | Cache               | Key                    | Invalidation          | Safety invariant                                          |
/// |---------------------|------------------------|-----------------------|-----------------------------------------------------------|
/// | `constrain_cache`   | `(TyId, TyId)`         | Never (per-file life) | Safe: all constraints already propagated through the pinned variable |
/// | `neg_cache`         | `TyId → TyId`          | Never (per-file life) | Unaffected: keys are inner TyIds, not compacted variables |
/// | `prim_cache`        | `PrimitiveTy → TyId`   | Never (per-file life) | Unaffected: keys are primitives, not variables             |
/// | `inter_var_cache`   | `TyId → bool`          | Never (per-file life) | Conservative: may treat concrete as variable (false positive), sound but over-constraining |
/// | `union_member_cache`| `(TyId, TyId)`         | Never (per-file life) | Unaffected: union structure is immutable once allocated    |
/// | `variable_free`     | `TyId`                 | Explicitly updated    | Updated during compaction via `try_mark_variable_free`    |
#[derive(Debug, Clone)]
pub(crate) struct TypeTable {
    pub(crate) storage: TypeStorage,

    /// Cache (sub, sup) pairs already processed by constrain() to avoid cycles.
    /// Intentionally never cleared between SCC groups: extrusion creates fresh
    /// vars linked to old ones via constrain(), and re-processing those pairs
    /// would cause infinite loops across extrusion boundaries. The cache is
    /// scoped to the lifetime of the owning CheckCtx (one per file), so it
    /// doesn't grow across files.
    pub(crate) constrain_cache: FxHashSet<(TyId, TyId)>,

    /// Negation type cache for deduplication. Maps inner TyId → Neg(inner) TyId.
    /// Ensures that `alloc_concrete(Neg(x))` returns the same TyId for the same
    /// `x`, which is critical for union absorption in constrain_lhs_inter:
    /// the absorption check uses TyId equality, so identical Neg types must share
    /// a TyId.
    pub(crate) neg_cache: FxHashMap<TyId, TyId>,

    /// Primitive type cache for deduplication.
    pub(crate) prim_cache: FxHashMap<PrimitiveTy, TyId>,

    /// Cache for `inter_contains_var`: maps TyId → whether it contains a
    /// variable (directly or through nested Inter). Valid for the lifetime
    /// of the inference run since type entries are append-only.
    pub(crate) inter_var_cache: FxHashMap<TyId, bool>,

    /// Cache for `union_contains_member`: stores (union_id, target_id) pairs
    /// that returned true. Valid for the lifetime of the inference run since
    /// Union structure is immutable once allocated.
    pub(crate) union_member_cache: FxHashSet<(TyId, TyId)>,

    /// TyIds whose entire reachable subtree contains no type variables —
    /// only concrete types and primitives. This is a structural property
    /// (level-independent) and never invalidated because TypeStorage is
    /// append-only. During extrusion, variable-free subtrees are returned
    /// as-is in O(1) — no clone, no recursion.
    pub(crate) variable_free: FxHashSet<TyId>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            storage: TypeStorage::new(),
            constrain_cache: FxHashSet::default(),
            neg_cache: FxHashMap::default(),
            prim_cache: FxHashMap::default(),
            inter_var_cache: FxHashMap::default(),
            union_member_cache: FxHashSet::default(),
            variable_free: FxHashSet::default(),
        }
    }

    /// Allocate a fresh type variable at the current level.
    pub fn new_var(&mut self) -> TyId {
        self.storage.new_var()
    }

    /// Allocate a concrete type and return its TyId.
    ///
    /// Normalizes negations via double-negation elimination and De Morgan:
    /// - `Neg(Neg(x))` → `x`
    /// - `Neg(Inter(a,b))` → `Union(Neg(a), Neg(b))`
    /// - `Neg(Union(a,b))` → `Inter(Neg(a), Neg(b))`
    pub fn alloc_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        if let Ty::Neg(inner) = &ty {
            // Deduplicate: return cached Neg if we've seen this inner before.
            if let Some(&cached) = self.neg_cache.get(inner) {
                return cached;
            }
            let inner_val = *inner;
            match self.storage.get(inner_val) {
                TypeEntry::Concrete(Ty::Neg(x)) => return *x, // ¬¬A → A
                TypeEntry::Concrete(Ty::Inter(a, b)) => {
                    // ¬(A ∧ B) → ¬A ∨ ¬B
                    let (a, b) = (*a, *b);
                    let neg_a = self.alloc_concrete(Ty::Neg(a));
                    let neg_b = self.alloc_concrete(Ty::Neg(b));
                    let id = self.storage.new_concrete(Ty::Union(neg_a, neg_b));
                    self.neg_cache.insert(inner_val, id);
                    return id;
                }
                TypeEntry::Concrete(Ty::Union(a, b)) => {
                    // ¬(A ∨ B) → ¬A ∧ ¬B
                    let (a, b) = (*a, *b);
                    let neg_a = self.alloc_concrete(Ty::Neg(a));
                    let neg_b = self.alloc_concrete(Ty::Neg(b));
                    let id = self.storage.new_concrete(Ty::Inter(neg_a, neg_b));
                    self.neg_cache.insert(inner_val, id);
                    return id;
                }
                _ => {}
            }
            let id = self.storage.new_concrete(ty);
            self.neg_cache.insert(inner_val, id);
            return id;
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

    /// Check if a TyId refers to a type variable (not a concrete type).
    pub fn is_var(&self, id: TyId) -> bool {
        matches!(self.storage.get(id), TypeEntry::Variable(_))
    }

    /// Get the concrete type for a TyId, panicking if it's a variable.
    pub fn expect_concrete(&self, id: TyId) -> Ty<TyId> {
        match self.storage.get(id) {
            TypeEntry::Concrete(t) => t.clone(),
            _ => unreachable!("expected concrete type for {id:?}"),
        }
    }

    /// If all children of the concrete type at `ty_id` are themselves
    /// variable-free, mark `ty_id` as variable-free too. No-op for variables.
    /// Called after extrusion short-circuits to populate the cache bottom-up.
    pub(crate) fn try_mark_variable_free(&mut self, ty_id: TyId) {
        let children_vf = match self.storage.get(ty_id) {
            TypeEntry::Variable(_) => return,
            TypeEntry::Concrete(ty) => match ty {
                Ty::Primitive(_) | Ty::TyVar(_) => true,
                Ty::List(e) => self.variable_free.contains(e),
                Ty::Lambda { param, body } => {
                    self.variable_free.contains(param) && self.variable_free.contains(body)
                }
                Ty::AttrSet(a) => {
                    a.fields.values().all(|v| self.variable_free.contains(v))
                        && a.dyn_ty.is_none_or(|d| self.variable_free.contains(&d))
                }
                Ty::Union(a, b) | Ty::Inter(a, b) => {
                    self.variable_free.contains(a) && self.variable_free.contains(b)
                }
                Ty::Neg(i) | Ty::Named(_, i) => self.variable_free.contains(i),
            },
        };
        if children_vf {
            self.variable_free.insert(ty_id);
        }
    }

    /// Compact fully-determined variables in the range `[slots_before..len)`.
    ///
    /// A variable is "pinned" when the same concrete TyId appears in both its
    /// lower_bounds and upper_bounds — meaning `ty <: var <: ty`, so `var = ty`.
    /// Such variables are effectively constants that extrusion would needlessly
    /// clone. Replacing them with the concrete type in-place eliminates the
    /// variable from the bounds graph without changing any TyId references.
    ///
    /// Falls back to `find_pinned_concrete` for cases where different TyIds
    /// hold the same primitive value (e.g. two separately-allocated `Int`
    /// entries).
    ///
    /// Returns `(pinned_count, deduped_count)` for logging.
    pub(crate) fn compact_pinned_variables(&mut self, slots_before: usize) -> (usize, usize) {
        let len = self.storage.len();
        let mut pinned_count = 0;
        let mut deduped_count = 0;

        for idx in slots_before..len {
            let id = TyId(idx as u32);

            let TypeEntry::Variable(v) = self.storage.get(id) else {
                continue;
            };

            // Fast path: check if the same concrete TyId appears in both bounds.
            // This handles non-primitive types too (Lambda, AttrSet, List, etc.).
            let mut found_pin: Option<TyId> = None;
            for &lb in &v.lower_bounds {
                if matches!(self.storage.get(lb), TypeEntry::Concrete(_)) {
                    for &ub in &v.upper_bounds {
                        if lb == ub {
                            found_pin = Some(lb);
                            break;
                        }
                    }
                    if found_pin.is_some() {
                        break;
                    }
                }
            }

            if let Some(concrete_id) = found_pin {
                let ty = match self.storage.get(concrete_id) {
                    TypeEntry::Concrete(ty) => ty.clone(),
                    _ => unreachable!(),
                };
                self.storage.replace_var_with_concrete(id, ty);
                self.try_mark_variable_free(id);
                pinned_count += 1;
                continue;
            }

            // Slow path: check for primitive-value matching via find_pinned_concrete.
            // Different TyIds may hold the same Primitive value if they were
            // allocated separately (before prim_cache deduplication was in place
            // or from different allocation paths).
            let v_clone = v.clone();
            if let Some(pinned_ty) = self.find_pinned_concrete(&v_clone) {
                self.storage.replace_var_with_concrete(id, pinned_ty);
                self.try_mark_variable_free(id);
                pinned_count += 1;
                continue;
            }

            // Not pinned — deduplicate bounds to reduce subsequent walk costs.
            let lb_before = v.lower_bounds.len();
            let ub_before = v.upper_bounds.len();
            self.storage.dedup_bounds(id);
            if let TypeEntry::Variable(v_after) = self.storage.get(id) {
                if v_after.lower_bounds.len() < lb_before || v_after.upper_bounds.len() < ub_before
                {
                    deduped_count += 1;
                }
            }
        }

        (pinned_count, deduped_count)
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

    /// Like `resolve_to_concrete_id`, but returns `None` when lower bounds
    /// contain 2+ distinct type heads (indicating a genuine union like
    /// `int | string`). Returns `Some(first_concrete_id)` when all reachable
    /// concrete types share the same head constructor — multiple `List` bounds
    /// from different constraint paths are compatible, not a union.
    ///
    /// Used by poly_type_env construction where collapsing a union variable
    /// to a single member would lose type information.
    pub fn resolve_to_single_concrete_id(&self, ty_id: TyId) -> Option<TyId> {
        let mut visited = HashSet::new();
        let mut first_id: Option<TyId> = None;
        let mut head: Option<TypeHead> = None;
        if self.resolve_to_single_concrete_id_inner(ty_id, &mut visited, &mut first_id, &mut head) {
            first_id
        } else {
            None // 2+ distinct type heads found (genuine union)
        }
    }

    /// Returns `true` to continue searching, `false` when a second distinct
    /// type head is found (short-circuit).
    fn resolve_to_single_concrete_id_inner(
        &self,
        ty_id: TyId,
        visited: &mut HashSet<TyId>,
        first_id: &mut Option<TyId>,
        head: &mut Option<TypeHead>,
    ) -> bool {
        if !visited.insert(ty_id) {
            return true; // Cycle — skip.
        }
        match self.storage.get(ty_id) {
            TypeEntry::Concrete(ty) => {
                let this_head = TypeHead::of(ty);
                match *head {
                    Some(ref existing) if *existing != this_head => false,
                    Some(_) => true, // Same head — compatible, keep going.
                    None => {
                        *head = Some(this_head);
                        *first_id = Some(ty_id);
                        true
                    }
                }
            }
            TypeEntry::Variable(v) => {
                let bounds = v.lower_bounds.clone();
                for lb in bounds {
                    if !self.resolve_to_single_concrete_id_inner(lb, visited, first_id, head) {
                        return false;
                    }
                }
                true
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

    /// Like `find_concrete`, but if the result is an `Inter(α, C)` where
    /// exactly one member is a concrete non-Neg, non-variable type, return
    /// that member. This lets the overload resolver see through narrowing
    /// intersections: `Inter(α, Int)` → `Primitive(Int)`.
    ///
    /// Returns None for Inter types where no useful concrete member can be
    /// extracted (e.g. `Inter(α, ¬Null)`), so the overload resolver treats
    /// the type as not yet resolved.
    pub fn find_concrete_through_inter(&self, ty_id: TyId) -> Option<Ty<TyId>> {
        let ty = self.find_concrete(ty_id)?;
        match &ty {
            Ty::Inter(..) => unwrap_inter_concrete(&self.storage, &ty),
            _ => Some(ty),
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

/// If `ty` is `Inter(a, b)`, extract the "useful" concrete member for
/// overload/merge/has_field resolution. Returns the non-Neg, non-variable
/// member (primitives, attrsets, lists, lambdas). Recurses into nested
/// Inter types. Returns None if no useful concrete member is found.
fn unwrap_inter_concrete(storage: &TypeStorage, ty: &Ty<TyId>) -> Option<Ty<TyId>> {
    let Ty::Inter(a, b) = ty else { return None };

    // Try to get a "useful" type from each side: something that is concrete
    // and not a Neg or Named wrapper (negations are constraints, not types you
    // can do overload resolution on; Named is transparent).
    let useful_from = |id: TyId| -> Option<Ty<TyId>> {
        match storage.get(id) {
            TypeEntry::Concrete(c @ Ty::Inter(..)) => unwrap_inter_concrete(storage, c),
            TypeEntry::Concrete(Ty::Named(_, inner)) => {
                // See through Named wrappers to find the useful concrete type.
                match storage.get(*inner) {
                    TypeEntry::Concrete(c @ Ty::Inter(..)) => unwrap_inter_concrete(storage, c),
                    TypeEntry::Concrete(Ty::Neg(_)) => None,
                    TypeEntry::Concrete(c) => Some(c.clone()),
                    TypeEntry::Variable(_) => None,
                }
            }
            TypeEntry::Concrete(Ty::Neg(_)) => None, // skip negations
            TypeEntry::Concrete(c) => Some(c.clone()),
            TypeEntry::Variable(_) => None,
        }
    };

    useful_from(*a).or_else(|| useful_from(*b))
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

    // NOTE: resolve_to_concrete_id returns the first concrete bound when
    // multiple exist, which can lose information for unions. The infer.rs
    // call site uses resolve_to_single_concrete_id instead, which compares
    // type heads to detect genuine unions (different constructors) while
    // still resolving compatible multi-bound variables (same constructor).

    #[test]
    fn resolve_to_single_concrete_id_single_bound() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        tt.storage.add_lower_bound(var, int_ty);

        // Single concrete lower bound — resolves normally.
        assert_eq!(tt.resolve_to_single_concrete_id(var), Some(int_ty));
    }

    #[test]
    fn resolve_to_single_concrete_id_union_returns_none() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let string_ty = tt.alloc_prim(PrimitiveTy::String);
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_lower_bound(var, string_ty);

        // Two distinct primitive heads — genuine union, returns None.
        assert_eq!(tt.resolve_to_single_concrete_id(var), None);
    }

    #[test]
    fn resolve_to_single_concrete_id_compatible_bounds() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_elem = tt.alloc_prim(PrimitiveTy::Int);
        let list1 = tt.alloc_concrete(Ty::List(int_elem));
        let elem_var = tt.new_var();
        let list2 = tt.alloc_concrete(Ty::List(elem_var));
        tt.storage.add_lower_bound(var, list1);
        tt.storage.add_lower_bound(var, list2);

        // Both are List — same head constructor, returns first found.
        assert_eq!(tt.resolve_to_single_concrete_id(var), Some(list1));
    }

    #[test]
    fn resolve_to_single_concrete_id_transitive_union() {
        let mut tt = TypeTable::new();
        let outer = tt.new_var();
        let inner = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let string_ty = tt.alloc_prim(PrimitiveTy::String);

        // outer → inner → {int, string}
        tt.storage.add_lower_bound(outer, inner);
        tt.storage.add_lower_bound(inner, int_ty);
        tt.storage.add_lower_bound(inner, string_ty);

        // Transitively finds the union, returns None.
        assert_eq!(tt.resolve_to_single_concrete_id(outer), None);
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

    // ======================================================================
    // compact_pinned_variables tests
    // ======================================================================

    #[test]
    fn compact_same_tyid_in_both_bounds() {
        let mut tt = TypeTable::new();
        let slots_before = tt.storage.len();

        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let var = tt.new_var();
        // Pin: same TyId in lower and upper bounds.
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, int_ty);

        let (pinned, _) = tt.compact_pinned_variables(slots_before);
        assert_eq!(pinned, 1);
        // The variable slot should now be concrete.
        assert!(matches!(
            tt.storage.get(var),
            TypeEntry::Concrete(Ty::Primitive(PrimitiveTy::Int))
        ));
    }

    #[test]
    fn compact_same_tyid_non_primitive() {
        let mut tt = TypeTable::new();
        let slots_before = tt.storage.len();

        let elem = tt.alloc_prim(PrimitiveTy::Int);
        let list_ty = tt.alloc_concrete(Ty::List(elem));
        let var = tt.new_var();
        // Pin: same List TyId in both bounds.
        tt.storage.add_lower_bound(var, list_ty);
        tt.storage.add_upper_bound(var, list_ty);

        let (pinned, _) = tt.compact_pinned_variables(slots_before);
        assert_eq!(pinned, 1);
        assert!(matches!(
            tt.storage.get(var),
            TypeEntry::Concrete(Ty::List(_))
        ));
    }

    #[test]
    fn compact_different_bounds_not_compacted() {
        let mut tt = TypeTable::new();
        let slots_before = tt.storage.len();

        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let string_ty = tt.alloc_prim(PrimitiveTy::String);
        let var = tt.new_var();
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, string_ty);

        let (pinned, _) = tt.compact_pinned_variables(slots_before);
        assert_eq!(pinned, 0);
        // Should still be a variable.
        assert!(matches!(tt.storage.get(var), TypeEntry::Variable(_)));
    }

    #[test]
    fn compact_only_lower_bounds_not_compacted() {
        let mut tt = TypeTable::new();
        let slots_before = tt.storage.len();

        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        let var = tt.new_var();
        tt.storage.add_lower_bound(var, int_ty);
        // No upper bounds.

        let (pinned, _) = tt.compact_pinned_variables(slots_before);
        assert_eq!(pinned, 0);
        assert!(matches!(tt.storage.get(var), TypeEntry::Variable(_)));
    }

    #[test]
    fn compact_primitive_value_match_different_tyids() {
        let mut tt = TypeTable::new();

        // Allocate two separate Int TyIds by bypassing the prim_cache.
        let int1 = tt.storage.new_concrete(Ty::Primitive(PrimitiveTy::Int));
        let int2 = tt.storage.new_concrete(Ty::Primitive(PrimitiveTy::Int));
        assert_ne!(int1, int2, "must be distinct TyIds for this test");

        let slots_before = tt.storage.len();
        let var = tt.new_var();
        tt.storage.add_lower_bound(var, int1);
        tt.storage.add_upper_bound(var, int2);

        // The fast path (same TyId) won't match, but find_pinned_concrete
        // should catch same-primitive-value.
        let (pinned, _) = tt.compact_pinned_variables(slots_before);
        assert_eq!(pinned, 1);
        assert!(matches!(
            tt.storage.get(var),
            TypeEntry::Concrete(Ty::Primitive(PrimitiveTy::Int))
        ));
    }

    #[test]
    fn dedup_bounds_removes_duplicates() {
        let mut tt = TypeTable::new();
        let var = tt.new_var();
        let int_ty = tt.alloc_prim(PrimitiveTy::Int);

        // Add duplicates.
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, int_ty);
        tt.storage.add_upper_bound(var, int_ty);

        tt.storage.dedup_bounds(var);

        let v = tt.storage.get_var(var).unwrap();
        assert_eq!(v.lower_bounds.len(), 1);
        assert_eq!(v.upper_bounds.len(), 1);
    }

    #[test]
    fn compact_marks_variable_free() {
        let mut tt = TypeTable::new();
        let slots_before = tt.storage.len();

        let int_ty = tt.alloc_prim(PrimitiveTy::Int);
        // Mark the primitive as variable-free (normally done during inference).
        tt.variable_free.insert(int_ty);

        let var = tt.new_var();
        tt.storage.add_lower_bound(var, int_ty);
        tt.storage.add_upper_bound(var, int_ty);

        assert!(!tt.variable_free.contains(&var));
        tt.compact_pinned_variables(slots_before);
        // After compaction, the slot is now Concrete(Int) whose child (int_ty)
        // is variable-free, so the slot itself should be marked variable-free.
        assert!(tt.variable_free.contains(&var));
    }
}
