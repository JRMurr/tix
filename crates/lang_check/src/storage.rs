// ==============================================================================
// Bounds-based Type Storage for SimpleSub
// ==============================================================================
//
// Replaces the old union-find storage with directional bounds tracking.
// Each type variable tracks lower bounds (types that flow into it) and
// upper bounds (types it flows into). Concrete types are stored directly.

use rustc_hash::FxHashSet;
use smallvec::SmallVec;

use super::TyId;
use lang_ty::Ty;

/// A type variable with directional bounds and a level for let-polymorphism.
#[derive(Debug, Clone)]
pub struct TypeVariable {
    /// Types that flow INTO this variable (produces union in positive position).
    pub lower_bounds: SmallVec<[TyId; 4]>,
    /// Types this variable flows INTO (produces intersection in negative position).
    pub upper_bounds: SmallVec<[TyId; 4]>,
    /// The binding level — used to determine which variables are polymorphic.
    /// Variables created at a deeper level than the current scope are generalizable.
    pub level: u32,
}

/// Each slot in the type storage is either a variable (with bounds) or a concrete type.
#[derive(Debug, Clone)]
pub enum TypeEntry {
    Variable(TypeVariable),
    Concrete(Ty<TyId>),
}

#[derive(Debug, Clone)]
pub struct TypeStorage {
    entries: Vec<TypeEntry>,
    pub(crate) current_level: u32,
    /// Pairs recorded by `constrain_equal`. Used at canonicalization time to
    /// build a DSU so equivalent TyIds emit the same `OutputTy::TyVar(id)`
    /// and thus collapse to a single free variable under `normalize_vars`.
    /// Without this, `{ x ? null }: let r = x; in r` exports with the param
    /// slot and body slot as distinct free vars, severing caller-side
    /// polymorphism across file boundaries.
    pub(crate) equiv_pairs: Vec<(TyId, TyId)>,
    /// Pattern-field name slots that received a `? default` lower bound (e.g.
    /// `{ x ? null }: ...`). The Negative-polarity empty-fallback in
    /// canonicalization skips these slots' lower bounds — defaults represent
    /// the parameter accepting `null` *as input*, not a declared parameter
    /// type. Without this filter, a body like `toString x` (no concrete upper
    /// bound on `x`) would collapse the exported param type to the default's
    /// type instead of staying polymorphic across file boundaries.
    ///
    /// Distinct from the stub-declared union case (`val f :: (int|string) -> bool`),
    /// which adds lower bounds via `apply_type_annotation` and is *not* marked
    /// here — the empty-fallback continues to expand those.
    pub(crate) default_marked_params: FxHashSet<TyId>,
}

impl TypeStorage {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            current_level: 0,
            equiv_pairs: Vec::new(),
            default_marked_params: FxHashSet::default(),
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            entries: Vec::with_capacity(cap),
            current_level: 0,
            equiv_pairs: Vec::new(),
            default_marked_params: FxHashSet::default(),
        }
    }

    /// Record that `a` and `b` are considered equal by `constrain_equal`.
    /// Self-pairs are dropped (no-op for the DSU).
    pub fn record_equiv(&mut self, a: TyId, b: TyId) {
        if a != b {
            self.equiv_pairs.push((a, b));
        }
    }

    /// Mark a pattern-field name slot as having received a `? default`
    /// lower bound. Idempotent. Consulted by canonicalization's Negative
    /// empty-fallback to skip default-derived bounds.
    pub fn mark_default_param(&mut self, id: TyId) {
        self.default_marked_params.insert(id);
    }

    /// True iff `id` was marked by `mark_default_param`.
    pub fn is_default_marked_param(&self, id: TyId) -> bool {
        self.default_marked_params.contains(&id)
    }

    /// Allocate a fresh type variable at the current level.
    pub fn new_var(&mut self) -> TyId {
        let id = TyId(self.entries.len() as u32);
        self.entries.push(TypeEntry::Variable(TypeVariable {
            lower_bounds: SmallVec::new(),
            upper_bounds: SmallVec::new(),
            level: self.current_level,
        }));
        id
    }

    /// Store a concrete (non-variable) type and return its TyId.
    pub fn new_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        let id = TyId(self.entries.len() as u32);
        self.entries.push(TypeEntry::Concrete(ty));
        id
    }

    /// Get the entry for a TyId.
    pub fn get(&self, id: TyId) -> &TypeEntry {
        &self.entries[id.0 as usize]
    }

    /// Get a mutable reference to the entry. Used internally.
    fn get_mut(&mut self, id: TyId) -> &mut TypeEntry {
        &mut self.entries[id.0 as usize]
    }

    /// If `id` is a variable, return a reference to its TypeVariable.
    pub fn get_var(&self, id: TyId) -> Option<&TypeVariable> {
        match self.get(id) {
            TypeEntry::Variable(v) => Some(v),
            TypeEntry::Concrete(_) => None,
        }
    }

    /// Record that `bound` is a lower bound of variable `var` (bound <: var).
    pub fn add_lower_bound(&mut self, var: TyId, bound: TyId) {
        match self.get_mut(var) {
            TypeEntry::Variable(v) => v.lower_bounds.push(bound),
            TypeEntry::Concrete(_) => {
                debug_assert!(false, "add_lower_bound called on concrete type {var:?}");
            }
        }
    }

    /// Record that `bound` is an upper bound of variable `var` (var <: bound).
    pub fn add_upper_bound(&mut self, var: TyId, bound: TyId) {
        match self.get_mut(var) {
            TypeEntry::Variable(v) => v.upper_bounds.push(bound),
            TypeEntry::Concrete(_) => {
                debug_assert!(false, "add_upper_bound called on concrete type {var:?}");
            }
        }
    }

    /// Update the level of a variable. Used to lift pre-allocated vars
    /// to the SCC group level so they are correctly generalizable.
    pub fn set_var_level(&mut self, id: TyId, level: u32) {
        match self.get_mut(id) {
            TypeEntry::Variable(v) => v.level = level,
            TypeEntry::Concrete(_) => {
                debug_assert!(false, "set_var_level called on concrete type {id:?}");
            }
        }
    }

    pub fn enter_level(&mut self) {
        self.current_level += 1;
    }

    pub fn exit_level(&mut self) {
        assert!(self.current_level > 0, "exit_level called at level 0");
        self.current_level -= 1;
    }

    /// Replace a Variable entry with a Concrete entry in-place.
    ///
    /// The TyId remains valid — all existing references (bounds, caches) that
    /// point to this slot now see a Concrete type instead of a Variable. This
    /// is the core primitive for bounds graph compaction: fully-determined
    /// variables (pinned between identical concrete bounds) become constants.
    pub fn replace_var_with_concrete(&mut self, id: TyId, ty: Ty<TyId>) {
        debug_assert!(matches!(self.get(id), TypeEntry::Variable(_)));
        *self.get_mut(id) = TypeEntry::Concrete(ty);
    }

    /// Sort and deduplicate the bounds vectors of a variable. No-op for
    /// concrete entries. Reduces memory and speeds up subsequent bounds walks
    /// (extrusion, constraint propagation) by removing redundant entries.
    pub fn dedup_bounds(&mut self, id: TyId) {
        if let TypeEntry::Variable(v) = self.get_mut(id) {
            v.lower_bounds.sort_unstable_by_key(|t| t.0);
            v.lower_bounds.dedup();
            v.upper_bounds.sort_unstable_by_key(|t| t.0);
            v.upper_bounds.dedup();
        }
    }

    /// Number of entries (variables + concrete types) in the storage.
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}
