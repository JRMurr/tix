// ==============================================================================
// Bounds-based Type Storage for SimpleSub
// ==============================================================================
//
// Replaces the old union-find storage with directional bounds tracking.
// Each type variable tracks lower bounds (types that flow into it) and
// upper bounds (types it flows into). Concrete types are stored directly.

use super::TyId;
use lang_ty::Ty;

/// A type variable with directional bounds and a level for let-polymorphism.
#[derive(Debug, Clone)]
pub struct TypeVariable {
    /// Types that flow INTO this variable (produces union in positive position).
    pub lower_bounds: Vec<TyId>,
    /// Types this variable flows INTO (produces intersection in negative position).
    pub upper_bounds: Vec<TyId>,
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
    pub current_level: u32,
}

impl TypeStorage {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            current_level: 0,
        }
    }

    /// Allocate a fresh type variable at the current level.
    pub fn new_var(&mut self) -> TyId {
        let id = TyId(self.entries.len() as u32);
        self.entries.push(TypeEntry::Variable(TypeVariable {
            lower_bounds: Vec::new(),
            upper_bounds: Vec::new(),
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
            TypeEntry::Concrete(_) => panic!("add_lower_bound called on concrete type {var:?}"),
        }
    }

    /// Record that `bound` is an upper bound of variable `var` (var <: bound).
    pub fn add_upper_bound(&mut self, var: TyId, bound: TyId) {
        match self.get_mut(var) {
            TypeEntry::Variable(v) => v.upper_bounds.push(bound),
            TypeEntry::Concrete(_) => panic!("add_upper_bound called on concrete type {var:?}"),
        }
    }

    /// Update the level of a variable. Used to lift pre-allocated vars
    /// to the SCC group level so they are correctly generalizable.
    pub fn set_var_level(&mut self, id: TyId, level: u32) {
        match self.get_mut(id) {
            TypeEntry::Variable(v) => v.level = level,
            TypeEntry::Concrete(_) => panic!("set_var_level called on concrete type {id:?}"),
        }
    }

    pub fn enter_level(&mut self) {
        self.current_level += 1;
    }

    pub fn exit_level(&mut self) {
        assert!(self.current_level > 0, "exit_level called at level 0");
        self.current_level -= 1;
    }
}
