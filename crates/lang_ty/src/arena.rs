// ==============================================================================
// TypeArena — arena-interned OutputTy storage with hash-consing
// ==============================================================================
//
// Replaces Arc<OutputTy>-based TyRef with arena-indexed TyRef (4-byte Idx).
// Each unique OutputTy is stored once; structurally identical types share the
// same index. This eliminates per-node allocation overhead, enables O(1)
// equality via index comparison, and improves cache locality.

use std::fmt;
use std::ops::{ControlFlow, Index};
use std::sync::Arc;

use crate::arc_ty::{
    needs_parens_in_intersection_member, needs_parens_in_lambda_param, needs_parens_in_neg,
    needs_parens_in_union_member, tyvar_name, DisplayConfig, UNKNOWN_TYVAR,
};
use crate::{AttrSetTy, OutputTy, Substitutions};
use la_arena::{Arena, Idx};
use rustc_hash::{FxHashMap, FxHashSet};

/// Compact 4-byte index into a TypeArena. Copy, no atomic refcounting.
pub type TyRef = Idx<OutputTy>;

// ==============================================================================
// TypeArena
// ==============================================================================

/// Arena-allocated output type storage with hash-consing.
///
/// All OutputTy nodes are stored in a contiguous Vec (via la_arena::Arena).
/// The `intern` map ensures structurally identical nodes get the same index.
#[derive(Clone)]
pub struct TypeArena {
    inner: Arena<OutputTy>,
    /// Hash-consing: structurally identical types get the same index.
    /// Key is the OutputTy (which contains TyRef indices — cheap to hash).
    intern: FxHashMap<OutputTy, TyRef>,
}

impl TypeArena {
    pub fn new() -> Self {
        Self {
            inner: Arena::new(),
            intern: FxHashMap::default(),
        }
    }

    /// Intern a type node. Returns existing index if structurally identical
    /// node already exists, otherwise allocates and returns new index.
    pub fn intern(&mut self, node: OutputTy) -> TyRef {
        match self.intern.entry(node) {
            std::collections::hash_map::Entry::Occupied(e) => *e.get(),
            std::collections::hash_map::Entry::Vacant(e) => {
                let id = self.inner.alloc(e.key().clone());
                *e.insert(id)
            }
        }
    }

    /// Look up a type by index.
    pub fn get(&self, ty: TyRef) -> &OutputTy {
        &self.inner[ty]
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    // ==========================================================================
    // Display
    // ==========================================================================

    /// Create a displayable wrapper for a type.
    pub fn display(&self, ty: TyRef) -> TypeDisplay<'_> {
        TypeDisplay { arena: self, ty }
    }

    /// Render the type with truncation limits applied.
    pub fn display_truncated(&self, ty: TyRef, config: &DisplayConfig) -> String {
        if config.is_unlimited() {
            return format!("{}", self.display(ty));
        }
        let mut buf = String::new();
        let mut state = TruncState {
            config,
            bytes_written: 0,
            budget_exceeded: false,
        };
        self.write_truncated(ty, &mut buf, &mut state, 0);
        buf
    }

    // ==========================================================================
    // Traversal / query methods (moved from impl OutputTy)
    // ==========================================================================

    /// Returns true if this type or any child contains a TyVar.
    pub fn has_type_vars(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| matches!(node, OutputTy::TyVar(_)))
    }

    /// Normalize all ty vars to start from 0 instead of the original indices.
    pub fn normalize_vars(&mut self, ty: TyRef) -> TyRef {
        // Extern types are already finalized in their source arena.
        if matches!(self[ty], OutputTy::Extern(_)) {
            return ty;
        }
        let free_vars = self.free_type_vars(ty);

        // Concrete types with no TyVar nodes are already normalized.
        if free_vars.is_empty() {
            return ty;
        }

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, i as u32))
            .collect();

        // Handle root TyVar directly.
        if let OutputTy::TyVar(x) = self[ty] {
            return self.intern(OutputTy::TyVar(*subs.get(&x).unwrap()));
        }

        let mut cache = FxHashMap::default();
        self.normalize_inner_cached(ty, &subs, &mut cache)
    }

    /// Memoized normalize_inner that caches by TyRef identity.
    pub(crate) fn normalize_inner_cached(
        &mut self,
        ty: TyRef,
        subs: &Substitutions,
        cache: &mut FxHashMap<TyRef, TyRef>,
    ) -> TyRef {
        if let Some(&cached) = cache.get(&ty) {
            return cached;
        }
        let node = self[ty].clone();
        let result = lang_ast::stack::with_stack(|| {
            if let OutputTy::TyVar(x) = &node {
                return self.intern(OutputTy::TyVar(*subs.get(x).unwrap()));
            }
            let new_node =
                node.map_children(&mut |child| self.normalize_inner_cached(child, subs, cache));
            self.intern(new_node)
        });
        cache.insert(ty, result);
        result
    }

    /// Check if `normalize_replacing_unknown` would actually mutate the arena.
    /// Returns false when the type has no free vars and isn't a bare TyVar,
    /// meaning normalization would return the input unchanged.
    pub fn needs_var_normalization(&self, ty: TyRef) -> bool {
        if matches!(self[ty], OutputTy::Extern(_)) {
            return false;
        }
        if matches!(self[ty], OutputTy::TyVar(_)) {
            return true;
        }
        !self.free_type_vars(ty).is_empty()
    }

    /// Like `normalize_vars`, but displays `?` when the entire type is a bare
    /// type variable (meaning "unconstrained / unknown").
    pub fn normalize_replacing_unknown(&mut self, ty: TyRef) -> TyRef {
        if matches!(self[ty], OutputTy::Extern(_)) {
            return ty;
        }
        if matches!(self[ty], OutputTy::TyVar(_)) {
            return self.intern(OutputTy::TyVar(UNKNOWN_TYVAR));
        }
        self.normalize_vars(ty)
    }

    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self, ty: TyRef) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = FxHashSet::default();
        let mut visited = FxHashSet::default();
        self.collect_free_type_vars(ty, &mut result, &mut seen, &mut visited);
        result
    }

    fn collect_free_type_vars(
        &self,
        ty: TyRef,
        result: &mut Vec<u32>,
        seen: &mut FxHashSet<u32>,
        visited: &mut FxHashSet<TyRef>,
    ) {
        if let OutputTy::Extern(owned) = &self[ty] {
            // Delegate to the external arena for its free vars.
            let ext_vars = owned.arena.free_type_vars(owned.root);
            for v in ext_vars {
                if seen.insert(v) {
                    result.push(v);
                }
            }
            return;
        }
        if let OutputTy::TyVar(x) = self[ty] {
            if seen.insert(x) {
                result.push(x);
            }
            return;
        }
        lang_ast::stack::with_stack(|| {
            self[ty].for_each_child(&mut |child| {
                if visited.insert(child) {
                    self.collect_free_type_vars(child, result, seen, visited);
                }
            });
        });
    }

    /// Collect free type vars for an attrset's fields and dyn_ty.
    pub fn free_type_vars_attrset(&self, attr: &AttrSetTy<TyRef>) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = FxHashSet::default();
        let mut visited = FxHashSet::default();
        for &v in attr.fields.values() {
            self.collect_free_type_vars(v, &mut result, &mut seen, &mut visited);
        }
        if let Some(dyn_ty) = attr.dyn_ty {
            self.collect_free_type_vars(dyn_ty, &mut result, &mut seen, &mut visited);
        }
        result
    }

    /// Returns true if any Lambda has a non-primitive param type.
    pub fn has_non_primitive_lambda_param(&self, ty: TyRef) -> bool {
        let mut visited = FxHashSet::default();
        self.has_non_primitive_lambda_param_inner(ty, &mut visited)
    }

    fn has_non_primitive_lambda_param_inner(
        &self,
        ty: TyRef,
        visited: &mut FxHashSet<TyRef>,
    ) -> bool {
        let node = &self[ty];
        if let OutputTy::Lambda { param, .. } = node {
            if !matches!(self[*param], OutputTy::Primitive(_) | OutputTy::TyVar(_)) {
                return true;
            }
        }
        node.try_for_each_child(&mut |child| {
            if visited.insert(child) && self.has_non_primitive_lambda_param_inner(child, visited) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
    }

    /// Returns true if this type or any child contains a Union or Intersection.
    pub fn contains_union_or_intersection(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| {
            matches!(node, OutputTy::Union(_) | OutputTy::Intersection(_))
        })
    }

    /// Returns true if this type or any child contains an Intersection.
    pub fn contains_intersection(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| matches!(node, OutputTy::Intersection(_)))
    }

    /// Returns true if this type or any child contains a Neg.
    pub fn contains_neg(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| matches!(node, OutputTy::Neg(_)))
    }

    /// Returns true if this type is or contains Top or Bottom.
    pub fn contains_top_or_bottom(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| matches!(node, OutputTy::Top | OutputTy::Bottom))
    }

    /// Returns true if this type is or contains a bare TyVar outside Lambda params.
    pub fn contains_bare_tyvar(&self, ty: TyRef) -> bool {
        let mut visited = FxHashSet::default();
        self.contains_bare_tyvar_inner(ty, &mut visited)
    }

    fn contains_bare_tyvar_inner(&self, ty: TyRef, visited: &mut FxHashSet<TyRef>) -> bool {
        match &self[ty] {
            OutputTy::TyVar(_) => true,
            OutputTy::Lambda { body, .. } => {
                visited.insert(*body) && self.contains_bare_tyvar_inner(*body, visited)
            }
            node => node
                .try_for_each_child(&mut |child| {
                    if visited.insert(child) && self.contains_bare_tyvar_inner(child, visited) {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                })
                .is_break(),
        }
    }

    /// Returns true if any TyVar index appears in Lambda param position more
    /// than once across distinct Lambdas.
    pub fn has_shared_tyvar_across_lambda_params(&self, ty: TyRef) -> bool {
        let mut seen = FxHashSet::default();
        let mut visited = FxHashSet::default();
        self.check_shared_lambda_param_tyvars(ty, &mut seen, &mut visited)
    }

    fn check_shared_lambda_param_tyvars(
        &self,
        ty: TyRef,
        seen: &mut FxHashSet<u32>,
        visited: &mut FxHashSet<TyRef>,
    ) -> bool {
        match &self[ty] {
            OutputTy::Lambda { param, body } => {
                if let OutputTy::TyVar(idx) = self[*param] {
                    if !seen.insert(idx) {
                        return true;
                    }
                }
                (visited.insert(*param)
                    && self.check_shared_lambda_param_tyvars(*param, seen, visited))
                    || (visited.insert(*body)
                        && self.check_shared_lambda_param_tyvars(*body, seen, visited))
            }
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => false,
            node => node
                .try_for_each_child(&mut |child| {
                    if visited.insert(child)
                        && self.check_shared_lambda_param_tyvars(child, seen, visited)
                    {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                })
                .is_break(),
        }
    }

    /// Returns true if this type contains a Named wrapper.
    pub fn contains_named(&self, ty: TyRef) -> bool {
        self.any_node_matches(ty, &|node| matches!(node, OutputTy::Named(..)))
    }

    /// Unwrap Named wrappers to get at the structural type.
    pub fn unwrap_named(&self, ty: TyRef) -> TyRef {
        match &self[ty] {
            OutputTy::Named(_, inner) => self.unwrap_named(*inner),
            // Extern types may have Named at their root — but unwrapping
            // would cross arena boundaries. Return as-is; callers that need
            // to inspect the structure should match on Extern explicitly.
            _ => ty,
        }
    }

    /// Recursively flatten, deduplicate, and sort Union/Intersection members
    /// for order-insensitive comparison.
    pub fn normalize_set_ops(&mut self, ty: TyRef) -> TyRef {
        if matches!(self[ty], OutputTy::Extern(_)) {
            return ty;
        }
        let mut cache = FxHashMap::default();
        self.normalize_set_ops_cached(ty, &mut cache)
    }

    fn normalize_set_ops_cached(
        &mut self,
        ty: TyRef,
        cache: &mut FxHashMap<TyRef, TyRef>,
    ) -> TyRef {
        if let Some(&cached) = cache.get(&ty) {
            return cached;
        }

        // Clone only what's needed: members vec for Union/Intersection (to release
        // the borrow before calling &mut self methods), full node only for the
        // fallback case that needs map_children.
        let result = match &self[ty] {
            OutputTy::Union(members) => {
                let members = members.clone();
                let mut flat = Vec::new();
                self.flatten_set_op_cached(&members, &mut flat, cache, true);
                flat.sort_by(|a, b| self[*a].cmp(&self[*b]));
                flat.dedup();
                if flat.len() == 1 {
                    flat[0]
                } else {
                    self.intern(OutputTy::Union(flat))
                }
            }
            OutputTy::Intersection(members) => {
                let members = members.clone();
                let mut flat = Vec::new();
                self.flatten_set_op_cached(&members, &mut flat, cache, false);
                flat.sort_by(|a, b| self[*a].cmp(&self[*b]));
                flat.dedup();
                if flat.len() == 1 {
                    flat[0]
                } else {
                    self.intern(OutputTy::Intersection(flat))
                }
            }
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Top | OutputTy::Bottom => ty,
            _ => {
                let node = self[ty].clone();
                let new_node =
                    node.map_children(&mut |child| self.normalize_set_ops_cached(child, cache));
                self.intern(new_node)
            }
        };
        cache.insert(ty, result);
        result
    }

    fn flatten_set_op_cached(
        &mut self,
        members: &[TyRef],
        out: &mut Vec<TyRef>,
        cache: &mut FxHashMap<TyRef, TyRef>,
        is_union: bool,
    ) {
        for &m in members {
            let normalized = self.normalize_set_ops_cached(m, cache);
            let node = self[normalized].clone();
            let should_flatten = if is_union {
                matches!(node, OutputTy::Union(_))
            } else {
                matches!(node, OutputTy::Intersection(_))
            };
            if should_flatten {
                match node {
                    OutputTy::Union(inner) | OutputTy::Intersection(inner) => {
                        out.extend(inner);
                    }
                    _ => unreachable!(),
                }
            } else {
                out.push(normalized);
            }
        }
    }

    // ==========================================================================
    // Internal helpers
    // ==========================================================================

    /// Returns true if any node in this type tree matches `pred`.
    /// Short-circuits on first hit. Uses a visited set for DAG safety.
    fn any_node_matches(&self, ty: TyRef, pred: &impl Fn(&OutputTy) -> bool) -> bool {
        let mut visited = FxHashSet::default();
        self.any_node_matches_inner(ty, pred, &mut visited)
    }

    fn any_node_matches_inner(
        &self,
        ty: TyRef,
        pred: &impl Fn(&OutputTy) -> bool,
        visited: &mut FxHashSet<TyRef>,
    ) -> bool {
        let node = &self[ty];
        if let OutputTy::Extern(owned) = node {
            return owned.arena.any_node_matches(owned.root, pred);
        }
        if pred(node) {
            return true;
        }
        node.try_for_each_child(&mut |child| {
            if visited.insert(child) && self.any_node_matches_inner(child, pred, visited) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
    }

    // ==========================================================================
    // Compact — extract reachable subtree into a new arena
    // ==========================================================================

    /// Deep-copy a type and its reachable subtree into a new compact arena.
    pub fn compact(&self, root: TyRef) -> (TypeArena, TyRef) {
        let mut new_arena = TypeArena::new();
        let mut mapping: FxHashMap<TyRef, TyRef> = FxHashMap::default();
        let new_root = compact_inner(self, root, &mut new_arena, &mut mapping);
        (new_arena, new_root)
    }

    // ==========================================================================
    // Truncated display helpers
    // ==========================================================================

    fn write_truncated(
        &self,
        ty: TyRef,
        buf: &mut String,
        state: &mut TruncState<'_>,
        depth: usize,
    ) {
        if state.budget_exceeded {
            return;
        }

        let node = self[ty].clone();
        lang_ast::stack::with_stack(|| match &node {
            OutputTy::Extern(owned) => {
                owned.arena.write_truncated(owned.root, buf, state, depth);
            }
            OutputTy::TyVar(x) => {
                state.push(buf, &tyvar_name(*x));
            }
            OutputTy::Primitive(p) => {
                state.push(buf, &format!("{p}"));
            }
            OutputTy::Bottom => {
                state.push(buf, "never");
            }
            OutputTy::Top => {
                state.push(buf, "any");
            }
            OutputTy::Named(name, _) => {
                state.push(buf, name);
            }
            OutputTy::List(inner) => {
                if state.at_depth_limit(depth) {
                    state.push(buf, "[...]");
                } else {
                    state.push(buf, "[");
                    if !state.budget_exceeded {
                        self.write_truncated(*inner, buf, state, depth + 1);
                    }
                    if !state.budget_exceeded {
                        state.push(buf, "]");
                    }
                }
            }
            OutputTy::Lambda { param, body } => {
                if state.at_depth_limit(depth) {
                    state.push(buf, "... -> ...");
                } else {
                    if needs_parens_in_lambda_param(&self[*param]) {
                        state.push(buf, "(");
                        if !state.budget_exceeded {
                            self.write_truncated(*param, buf, state, depth + 1);
                        }
                        if !state.budget_exceeded {
                            state.push(buf, ")");
                        }
                    } else {
                        self.write_truncated(*param, buf, state, depth + 1);
                    }
                    if !state.budget_exceeded {
                        state.push(buf, " -> ");
                    }
                    if !state.budget_exceeded {
                        self.write_truncated(*body, buf, state, depth + 1);
                    }
                }
            }
            OutputTy::AttrSet(attr) => {
                if state.at_depth_limit(depth) {
                    let total =
                        attr.fields.len() + attr.dyn_ty.is_some() as usize + attr.open as usize;
                    state.push(buf, &format!("{{ ... {total} fields ... }}"));
                } else {
                    state.push(buf, "{ ");
                    let max_f = state.config.max_fields;
                    let mut count = 0;
                    let total_fields = attr.fields.len();
                    for (k, &v) in attr.fields.iter() {
                        if state.budget_exceeded {
                            return;
                        }
                        if max_f > 0 && count >= max_f {
                            let remaining = total_fields - count
                                + attr.dyn_ty.is_some() as usize
                                + attr.open as usize;
                            state.push(buf, &format!("... ({remaining} more)"));
                            state.push(buf, " }");
                            return;
                        }
                        if count > 0 {
                            state.push(buf, ", ");
                        }
                        let opt = if attr.optional_fields.contains(k) {
                            "?"
                        } else {
                            ""
                        };
                        state.push(buf, &format!("{k}{opt}: "));
                        if !state.budget_exceeded {
                            self.write_truncated(v, buf, state, depth + 1);
                        }
                        count += 1;
                    }
                    if let Some(dyn_ty) = attr.dyn_ty {
                        if !state.budget_exceeded {
                            if count > 0 {
                                state.push(buf, ", ");
                            }
                            state.push(buf, "_: ");
                            if !state.budget_exceeded {
                                self.write_truncated(dyn_ty, buf, state, depth + 1);
                            }
                        }
                    }
                    if attr.open && !state.budget_exceeded {
                        if count > 0 || attr.dyn_ty.is_some() {
                            state.push(buf, ", ");
                        }
                        state.push(buf, "...");
                    }
                    if !state.budget_exceeded {
                        state.push(buf, " }");
                    }
                }
            }
            OutputTy::Union(members) => {
                self.write_members_truncated(members, " | ", depth, buf, state, |arena, m| {
                    needs_parens_in_union_member(&arena[m])
                });
            }
            OutputTy::Intersection(members) => {
                self.write_members_truncated(members, " & ", depth, buf, state, |arena, m| {
                    needs_parens_in_intersection_member(&arena[m])
                });
            }
            OutputTy::Neg(inner) => {
                if needs_parens_in_neg(&self[*inner]) {
                    state.push(buf, "~(");
                    if !state.budget_exceeded {
                        self.write_truncated(*inner, buf, state, depth);
                    }
                    if !state.budget_exceeded {
                        state.push(buf, ")");
                    }
                } else {
                    state.push(buf, "~");
                    if !state.budget_exceeded {
                        self.write_truncated(*inner, buf, state, depth);
                    }
                }
            }
        });
    }

    fn write_members_truncated(
        &self,
        members: &[TyRef],
        separator: &str,
        depth: usize,
        buf: &mut String,
        state: &mut TruncState<'_>,
        needs_parens: impl Fn(&TypeArena, TyRef) -> bool,
    ) {
        if state.at_depth_limit(depth) {
            state.push(buf, "...");
            return;
        }
        let max_m = state.config.max_members;
        for (i, &m) in members.iter().enumerate() {
            if state.budget_exceeded {
                return;
            }
            if max_m > 0 && i >= max_m {
                let remaining = members.len() - i;
                state.push(buf, &format!("{separator}... ({remaining} more)"));
                return;
            }
            if i > 0 {
                state.push(buf, separator);
            }
            if needs_parens(self, m) {
                state.push(buf, "(");
                if !state.budget_exceeded {
                    self.write_truncated(m, buf, state, depth + 1);
                }
                if !state.budget_exceeded {
                    state.push(buf, ")");
                }
            } else {
                self.write_truncated(m, buf, state, depth + 1);
            }
        }
    }
}

impl fmt::Debug for TypeArena {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeArena({} entries)", self.inner.len())
    }
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

impl Index<TyRef> for TypeArena {
    type Output = OutputTy;
    fn index(&self, idx: TyRef) -> &OutputTy {
        &self.inner[idx]
    }
}

// ==============================================================================
// Compact helper (free function to avoid borrow issues)
// ==============================================================================

fn compact_inner(
    source: &TypeArena,
    ty: TyRef,
    target: &mut TypeArena,
    mapping: &mut FxHashMap<TyRef, TyRef>,
) -> TyRef {
    if let Some(&mapped) = mapping.get(&ty) {
        return mapped;
    }
    let node = source[ty].clone();
    // Extern nodes are preserved as-is: re-intern the Extern into the target
    // arena, keeping the Arc reference to the external arena alive.
    if matches!(node, OutputTy::Extern(_)) {
        let new_ref = target.intern(node);
        mapping.insert(ty, new_ref);
        return new_ref;
    }
    let new_node = node.map_children(&mut |child| compact_inner(source, child, target, mapping));
    let new_ref = target.intern(new_node);
    mapping.insert(ty, new_ref);
    new_ref
}

/// Import a type and its reachable subtree from a source arena into a target arena.
/// Used when canonicalizing Frozen types from imported file arenas.
pub fn import_from_arena(
    target: &mut TypeArena,
    source: &TypeArena,
    ty: TyRef,
    cache: &mut FxHashMap<TyRef, TyRef>,
) -> TyRef {
    if let Some(&cached) = cache.get(&ty) {
        return cached;
    }
    let node = source[ty].clone();
    let new_node = node.map_children(&mut |child| import_from_arena(target, source, child, cache));
    let result = target.intern(new_node);
    cache.insert(ty, result);
    result
}

// ==============================================================================
// OwnedTy — arena + index bundle for cross-file boundaries
// ==============================================================================

/// A self-contained type: the arena that owns the type nodes + a root index.
/// Used at cross-file boundaries (FileSignature, Frozen, import_types).
/// Cheap to clone (Arc refcount bump + Copy index).
#[derive(Clone)]
pub struct OwnedTy {
    pub arena: Arc<TypeArena>,
    pub root: TyRef,
}

impl OwnedTy {
    pub fn new(arena: Arc<TypeArena>, root: TyRef) -> Self {
        Self { arena, root }
    }

    /// Access the root OutputTy node.
    pub fn get(&self) -> &OutputTy {
        self.arena.get(self.root)
    }

    /// Create a compacted copy (small arena with only reachable subtree).
    pub fn compact(&self) -> OwnedTy {
        let (new_arena, new_root) = self.arena.compact(self.root);
        OwnedTy {
            arena: Arc::new(new_arena),
            root: new_root,
        }
    }

    /// Display with truncation config.
    pub fn display_truncated(&self, config: &DisplayConfig) -> String {
        self.arena.display_truncated(self.root, config)
    }
}

impl fmt::Debug for OwnedTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "OwnedTy({:?})", self.root)
    }
}

/// Identity-based equality: same arena (by Arc pointer) and same root index.
/// This is correct for inference — two Frozen types from the same import with
/// the same root are identical. Cross-arena comparison uses structurally_eq.
impl PartialEq for OwnedTy {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.arena, &other.arena) && self.root == other.root
    }
}

impl Eq for OwnedTy {}

impl std::hash::Hash for OwnedTy {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.arena) as usize).hash(state);
        self.root.hash(state);
    }
}

impl PartialOrd for OwnedTy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OwnedTy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let ptr_a = Arc::as_ptr(&self.arena) as usize;
        let ptr_b = Arc::as_ptr(&other.arena) as usize;
        ptr_a.cmp(&ptr_b).then_with(|| self.root.cmp(&other.root))
    }
}

impl OwnedTy {
    /// Structural cross-arena equality: compares two types from potentially
    /// different arenas by recursively comparing their OutputTy nodes.
    ///
    /// Unlike `PartialEq` (which is identity-based via `Arc::ptr_eq`), this
    /// compares the actual type structure. Two independently-constructed types
    /// with the same shape compare as equal.
    ///
    /// Used for convergence checks in fixpoint iteration and LSP signature
    /// change detection.
    pub fn structurally_eq(&self, other: &Self) -> bool {
        // Fast path: same arena and same root → identical.
        if Arc::ptr_eq(&self.arena, &other.arena) && self.root == other.root {
            return true;
        }
        structurally_eq_inner(
            &self.arena,
            self.root,
            &other.arena,
            other.root,
            &mut FxHashSet::default(),
        )
    }
}

/// Recursive structural equality with cycle detection.
///
/// The `visited` set tracks `(TyRef, TyRef)` pairs already compared to break
/// cycles (e.g. recursive types via Extern). If we encounter a pair we've
/// already seen, we assume equality — any structural difference would have
/// been caught on a different path through the type.
fn structurally_eq_inner(
    a_arena: &TypeArena,
    a: TyRef,
    b_arena: &TypeArena,
    b: TyRef,
    visited: &mut FxHashSet<(TyRef, TyRef)>,
) -> bool {
    if !visited.insert((a, b)) {
        return true; // cycle — assume equal
    }
    let a_node = &a_arena[a];
    let b_node = &b_arena[b];
    match (a_node, b_node) {
        (OutputTy::TyVar(x), OutputTy::TyVar(y)) => x == y,
        (OutputTy::Primitive(x), OutputTy::Primitive(y)) => x == y,
        (OutputTy::Bottom, OutputTy::Bottom) | (OutputTy::Top, OutputTy::Top) => true,
        (OutputTy::List(a_inner), OutputTy::List(b_inner)) => {
            structurally_eq_inner(a_arena, *a_inner, b_arena, *b_inner, visited)
        }
        (
            OutputTy::Lambda {
                param: ap,
                body: ab,
            },
            OutputTy::Lambda {
                param: bp,
                body: bb,
            },
        ) => {
            structurally_eq_inner(a_arena, *ap, b_arena, *bp, visited)
                && structurally_eq_inner(a_arena, *ab, b_arena, *bb, visited)
        }
        (OutputTy::AttrSet(a_attr), OutputTy::AttrSet(b_attr)) => {
            a_attr.open == b_attr.open
                && a_attr.optional_fields == b_attr.optional_fields
                && a_attr.fields.len() == b_attr.fields.len()
                && a_attr.fields.keys().eq(b_attr.fields.keys())
                && a_attr
                    .fields
                    .values()
                    .zip(b_attr.fields.values())
                    .all(|(av, bv)| structurally_eq_inner(a_arena, *av, b_arena, *bv, visited))
                && match (a_attr.dyn_ty, b_attr.dyn_ty) {
                    (Some(ad), Some(bd)) => {
                        structurally_eq_inner(a_arena, ad, b_arena, bd, visited)
                    }
                    (None, None) => true,
                    _ => false,
                }
        }
        (OutputTy::Union(am), OutputTy::Union(bm))
        | (OutputTy::Intersection(am), OutputTy::Intersection(bm)) => {
            am.len() == bm.len()
                && am
                    .iter()
                    .zip(bm.iter())
                    .all(|(a, b)| structurally_eq_inner(a_arena, *a, b_arena, *b, visited))
        }
        (OutputTy::Named(an, ai), OutputTy::Named(bn, bi)) => {
            an == bn && structurally_eq_inner(a_arena, *ai, b_arena, *bi, visited)
        }
        (OutputTy::Neg(ai), OutputTy::Neg(bi)) => {
            structurally_eq_inner(a_arena, *ai, b_arena, *bi, visited)
        }
        // Extern: follow through to the external arena.
        (OutputTy::Extern(a_owned), _) => {
            structurally_eq_inner(&a_owned.arena, a_owned.root, b_arena, b, visited)
        }
        (_, OutputTy::Extern(b_owned)) => {
            structurally_eq_inner(a_arena, a, &b_owned.arena, b_owned.root, visited)
        }
        _ => false,
    }
}

impl fmt::Display for OwnedTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.arena.display(self.root))
    }
}

// ==============================================================================
// TypeDisplay — Display wrapper that carries arena context
// ==============================================================================

pub struct TypeDisplay<'a> {
    arena: &'a TypeArena,
    ty: TyRef,
}

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_ty(self.arena, self.ty, f)
    }
}

fn write_ty(arena: &TypeArena, ty: TyRef, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    lang_ast::stack::with_stack(|| match &arena[ty] {
        OutputTy::Extern(owned) => write!(f, "{}", owned.arena.display(owned.root)),
        OutputTy::TyVar(x) => write!(f, "{}", tyvar_name(*x)),
        OutputTy::Primitive(p) => write!(f, "{p}"),
        OutputTy::List(inner) => {
            write!(f, "[{}]", arena.display(*inner))
        }
        OutputTy::Lambda { param, body } => {
            if needs_parens_in_lambda_param(&arena[*param]) {
                write!(f, "({}) -> {}", arena.display(*param), arena.display(*body))
            } else {
                write!(f, "{} -> {}", arena.display(*param), arena.display(*body))
            }
        }
        OutputTy::AttrSet(attr) => write_attrset_display(arena, attr, f),
        OutputTy::Union(members) => {
            for (i, &m) in members.iter().enumerate() {
                if i > 0 {
                    write!(f, " | ")?;
                }
                if needs_parens_in_union_member(&arena[m]) {
                    write!(f, "({})", arena.display(m))?;
                } else {
                    write!(f, "{}", arena.display(m))?;
                }
            }
            Ok(())
        }
        OutputTy::Intersection(members) => {
            for (i, &m) in members.iter().enumerate() {
                if i > 0 {
                    write!(f, " & ")?;
                }
                if needs_parens_in_intersection_member(&arena[m]) {
                    write!(f, "({})", arena.display(m))?;
                } else {
                    write!(f, "{}", arena.display(m))?;
                }
            }
            Ok(())
        }
        OutputTy::Named(name, _) => write!(f, "{name}"),
        OutputTy::Neg(inner) => {
            if needs_parens_in_neg(&arena[*inner]) {
                write!(f, "~({})", arena.display(*inner))
            } else {
                write!(f, "~{}", arena.display(*inner))
            }
        }
        OutputTy::Bottom => write!(f, "never"),
        OutputTy::Top => write!(f, "any"),
    })
}

fn write_attrset_display(
    arena: &TypeArena,
    attr: &AttrSetTy<TyRef>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    write!(f, "{{ ")?;
    let mut first = true;
    for (k, &v) in attr.fields.iter() {
        if !first {
            write!(f, ", ")?;
        }
        first = false;
        let opt = if attr.optional_fields.contains(k) {
            "?"
        } else {
            ""
        };
        write!(f, "{k}{opt}: {}", arena.display(v))?;
    }
    if let Some(dyn_ty) = attr.dyn_ty {
        if !first {
            write!(f, ", ")?;
        }
        first = false;
        write!(f, "_: {}", arena.display(dyn_ty))?;
    }
    if attr.open {
        if !first {
            write!(f, ", ")?;
        }
        write!(f, "...")?;
    }
    write!(f, " }}")
}

// ==============================================================================
// TruncState — truncation budget tracking
// ==============================================================================

struct TruncState<'a> {
    config: &'a DisplayConfig,
    bytes_written: usize,
    budget_exceeded: bool,
}

impl TruncState<'_> {
    fn at_depth_limit(&self, depth: usize) -> bool {
        self.config.max_depth > 0 && depth >= self.config.max_depth
    }

    fn push(&mut self, buf: &mut String, s: &str) -> bool {
        if self.budget_exceeded {
            return false;
        }
        let max = self.config.max_chars;
        if max > 0 && self.bytes_written + s.len() > max {
            // Floor the byte budget to a char boundary — slicing mid-codepoint
            // panics.
            let mut remaining = max.saturating_sub(self.bytes_written);
            while remaining > 0 && !s.is_char_boundary(remaining) {
                remaining -= 1;
            }
            if remaining > 0 {
                buf.push_str(&s[..remaining]);
            }
            buf.push_str("...");
            self.bytes_written = max;
            self.budget_exceeded = true;
            return false;
        }
        buf.push_str(s);
        self.bytes_written += s.len();
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{arc_ty, PrimitiveTy};

    /// Build a simple OwnedTy from a closure that populates an arena.
    fn make_owned(f: impl FnOnce(&mut TypeArena) -> TyRef) -> OwnedTy {
        let mut arena = TypeArena::new();
        let root = f(&mut arena);
        OwnedTy::new(Arc::new(arena), root)
    }

    /// Truncation cuts at a byte budget; a multibyte field name straddling the
    /// cut must not panic on a non-char-boundary slice.
    #[test]
    fn truncated_display_multibyte_no_panic() {
        let mut arena = TypeArena::new();
        let int = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
        let fields: std::collections::BTreeMap<smol_str::SmolStr, TyRef> = (0..30)
            .map(|i| (smol_str::SmolStr::from(format!("héllø_wörld_{i}")), int))
            .collect();
        let attrs = arena.intern(OutputTy::AttrSet(crate::AttrSetTy {
            fields,
            optional_fields: Default::default(),
            dyn_ty: None,
            open: false,
        }));

        // Sweep budgets so some cut lands mid-codepoint.
        for max_chars in 1..200 {
            let config = DisplayConfig {
                max_chars,
                ..DisplayConfig::inlay()
            };
            let _ = arena.display_truncated(attrs, &config);
        }
    }

    #[test]
    fn same_primitive_different_arenas() {
        let a = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        let b = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        assert!(!Arc::ptr_eq(&a.arena, &b.arena), "sanity: different arenas");
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn different_primitives() {
        let a = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        let b = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::String)));
        assert!(!a.structurally_eq(&b));
    }

    #[test]
    fn same_arena_fast_path() {
        let a = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        // Same arena and root — identity fast path.
        assert!(a.structurally_eq(&a));
    }

    #[test]
    fn lambda_structural_eq() {
        let a = make_owned(|arena| {
            let p = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            let b = arena.intern(OutputTy::Primitive(PrimitiveTy::String));
            arena.intern(OutputTy::Lambda { param: p, body: b })
        });
        let b = make_owned(|arena| {
            let p = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            let b = arena.intern(OutputTy::Primitive(PrimitiveTy::String));
            arena.intern(OutputTy::Lambda { param: p, body: b })
        });
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn lambda_different_body() {
        let a = make_owned(|arena| {
            let p = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            let b = arena.intern(OutputTy::Primitive(PrimitiveTy::String));
            arena.intern(OutputTy::Lambda { param: p, body: b })
        });
        let b = make_owned(|arena| {
            let p = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            let b = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::Lambda { param: p, body: b })
        });
        assert!(!a.structurally_eq(&b));
    }

    #[test]
    fn attrset_structural_eq() {
        let a = make_owned(|arena| arc_ty!(arena, { "x" : Int, "y" : String }));
        let b = make_owned(|arena| arc_ty!(arena, { "x" : Int, "y" : String }));
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn attrset_different_fields() {
        let a = make_owned(|arena| arc_ty!(arena, { "x" : Int }));
        let b = make_owned(|arena| arc_ty!(arena, { "y" : Int }));
        assert!(!a.structurally_eq(&b));
    }

    #[test]
    fn union_structural_eq() {
        let a = make_owned(|arena| {
            let members = vec![arc_ty!(arena, Int), arc_ty!(arena, String)];
            arena.intern(OutputTy::Union(members))
        });
        let b = make_owned(|arena| {
            let members = vec![arc_ty!(arena, Int), arc_ty!(arena, String)];
            arena.intern(OutputTy::Union(members))
        });
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn top_bottom_eq() {
        let a = make_owned(|arena| arena.intern(OutputTy::Top));
        let b = make_owned(|arena| arena.intern(OutputTy::Top));
        assert!(a.structurally_eq(&b));

        let c = make_owned(|arena| arena.intern(OutputTy::Bottom));
        let d = make_owned(|arena| arena.intern(OutputTy::Bottom));
        assert!(c.structurally_eq(&d));
        assert!(!a.structurally_eq(&c));
    }

    #[test]
    fn named_structural_eq() {
        let a = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::Named("Foo".into(), inner))
        });
        let b = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::Named("Foo".into(), inner))
        });
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn named_different_name() {
        let a = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::Named("Foo".into(), inner))
        });
        let b = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::Named("Bar".into(), inner))
        });
        assert!(!a.structurally_eq(&b));
    }

    #[test]
    fn neg_structural_eq() {
        let a = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Null));
            arena.intern(OutputTy::Neg(inner))
        });
        let b = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Null));
            arena.intern(OutputTy::Neg(inner))
        });
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn list_structural_eq() {
        let a = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::List(inner))
        });
        let b = make_owned(|arena| {
            let inner = arena.intern(OutputTy::Primitive(PrimitiveTy::Int));
            arena.intern(OutputTy::List(inner))
        });
        assert!(a.structurally_eq(&b));
    }

    #[test]
    fn tyvar_structural_eq() {
        let a = make_owned(|arena| arena.intern(OutputTy::TyVar(0)));
        let b = make_owned(|arena| arena.intern(OutputTy::TyVar(0)));
        assert!(a.structurally_eq(&b));

        let c = make_owned(|arena| arena.intern(OutputTy::TyVar(1)));
        assert!(!a.structurally_eq(&c));
    }

    #[test]
    fn extern_unwraps_transparently() {
        // Build an inner OwnedTy, then wrap it in Extern in another arena.
        // Structural eq should see through the Extern wrapper.
        let inner = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        let wrapped = make_owned(|arena| arena.intern(OutputTy::Extern(inner.clone())));
        let plain = make_owned(|arena| arena.intern(OutputTy::Primitive(PrimitiveTy::Int)));
        assert!(wrapped.structurally_eq(&plain));
        assert!(plain.structurally_eq(&wrapped));
    }
}

#[cfg(test)]
mod hegel_tests {
    use super::*;
    use crate::hegel_gen::{raw_tys, shuffle_set_ops};
    use crate::raw_ty::intern_raw;

    const DEPTH: u32 = 4;

    fn interned(tc: &hegel::TestCase) -> (TypeArena, TyRef) {
        let raw = tc.draw(raw_tys(DEPTH));
        let mut arena = TypeArena::new();
        let root = intern_raw(&mut arena, &raw);
        (arena, root)
    }

    /// Check the set-op normal form: flat, sorted, deduplicated, no singletons.
    fn assert_set_op_normal_form(arena: &TypeArena, ty: TyRef) {
        let node = &arena[ty];
        if let OutputTy::Union(members) | OutputTy::Intersection(members) = node {
            let is_union = matches!(node, OutputTy::Union(_));
            assert!(
                members.len() >= 2,
                "singleton set op: {}",
                arena.display(ty)
            );
            for pair in members.windows(2) {
                assert!(
                    arena[pair[0]] < arena[pair[1]],
                    "unsorted or duplicate members in {}",
                    arena.display(ty)
                );
            }
            for m in members {
                let nested = match &arena[*m] {
                    OutputTy::Union(_) => is_union,
                    OutputTy::Intersection(_) => !is_union,
                    _ => false,
                };
                assert!(!nested, "nested same-kind set op in {}", arena.display(ty));
            }
        }
        let mut children = Vec::new();
        node.map_children(&mut |c| {
            children.push(c);
            c
        });
        for child in children {
            assert_set_op_normal_form(arena, child);
        }
    }

    #[hegel::test]
    fn normalize_set_ops_idempotent(tc: hegel::TestCase) {
        let (mut arena, ty) = interned(&tc);
        let once = arena.normalize_set_ops(ty);
        let twice = arena.normalize_set_ops(once);
        assert_eq!(once, twice);
    }

    #[hegel::test]
    fn normalize_set_ops_is_normal_form(tc: hegel::TestCase) {
        let (mut arena, ty) = interned(&tc);
        let result = arena.normalize_set_ops(ty);
        assert_set_op_normal_form(&arena, result);
    }

    /// Member order in the source type must not affect the normalized result.
    #[hegel::test]
    fn normalize_set_ops_permutation_invariant(tc: hegel::TestCase) {
        let raw = tc.draw(raw_tys(DEPTH));
        let mut shuffled = raw.clone();
        shuffle_set_ops(&tc, &mut shuffled);

        let mut arena = TypeArena::new();
        let a = intern_raw(&mut arena, &raw);
        let b = intern_raw(&mut arena, &shuffled);
        let a = arena.normalize_set_ops(a);
        let b = arena.normalize_set_ops(b);
        assert_eq!(a, b, "{} vs {}", arena.display(a), arena.display(b));
    }

    #[hegel::test]
    fn normalize_vars_idempotent(tc: hegel::TestCase) {
        let (mut arena, ty) = interned(&tc);
        let once = arena.normalize_vars(ty);
        let twice = arena.normalize_vars(once);
        assert_eq!(once, twice);
    }

    #[hegel::test]
    fn normalize_vars_numbers_from_zero(tc: hegel::TestCase) {
        let (mut arena, ty) = interned(&tc);
        let result = arena.normalize_vars(ty);
        let vars = arena.free_type_vars(result);
        let expected: Vec<u32> = (0..vars.len() as u32).collect();
        assert_eq!(vars, expected);
    }

    /// Renaming variables in the raw tree (injectively) must not change the
    /// normalized form.
    #[hegel::test]
    fn normalize_vars_alpha_invariant(tc: hegel::TestCase) {
        let raw = tc.draw(raw_tys(DEPTH));
        let offset = tc.draw(hegel::generators::integers::<u32>().max_value(1000));
        let mut num = offset as usize;
        let renamed = raw.offset_free_vars(&mut num);

        let mut arena = TypeArena::new();
        let a = intern_raw(&mut arena, &raw);
        let b = intern_raw(&mut arena, &renamed);
        let a = arena.normalize_vars(a);
        let b = arena.normalize_vars(b);
        assert_eq!(a, b, "{} vs {}", arena.display(a), arena.display(b));
    }

    #[hegel::test]
    fn compact_preserves_structure(tc: hegel::TestCase) {
        let (arena, ty) = interned(&tc);
        let (small, root) = arena.compact(ty);
        assert!(small.len() <= arena.len());
        let before = OwnedTy::new(Arc::new(arena), ty);
        let after = OwnedTy::new(Arc::new(small), root);
        assert!(before.structurally_eq(&after));
    }

    #[hegel::test]
    fn intern_is_hash_consed(tc: hegel::TestCase) {
        let raw = tc.draw(raw_tys(DEPTH));
        let mut arena = TypeArena::new();
        let a = intern_raw(&mut arena, &raw);
        let len = arena.len();
        let b = intern_raw(&mut arena, &raw);
        assert_eq!(a, b);
        assert_eq!(arena.len(), len, "re-interning allocated new nodes");
    }
}
