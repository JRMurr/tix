// ==============================================================================
// Inference Orchestration — SCC groups, generalization, extrude
// ==============================================================================
//
// This module drives the overall inference process: iterating over SCC groups,
// inferring each definition, resolving pending constraints, and generalizing
// type variables via SimpleSub's level-based approach (extrude).

use std::collections::{HashMap, HashSet};

use super::{CheckCtx, InferenceError, InferenceResult, LocatedError, TyId};
use crate::collect::{canonicalize_standalone, Collector};
use crate::diagnostic;
use crate::diagnostic::TixDiagnostic;
use crate::infer_expr::{BinConstraint, PendingMerge, PendingOverload};
use crate::storage::TypeEntry;
use lang_ast::nameres::{DependentGroup, GroupedDefs};
use lang_ast::OverloadBinOp;
use lang_ty::simplify::simplify;
use lang_ty::{AttrSetTy, PrimitiveTy, Ty};

/// Result of attempting to resolve a single overloaded binary operation.
enum OverloadProgress {
    /// Both operands were concrete; the return type has been fully constrained.
    FullyResolved,
    /// Some constraints were added (e.g. Number upper bound) but the overload
    /// still needs another iteration to fully resolve.
    PartialProgress,
    /// No new constraints could be added — operands are still unknown.
    NoProgress,
}

impl CheckCtx<'_> {
    pub fn infer_prog(self, groups: GroupedDefs) -> Result<InferenceResult, TixDiagnostic> {
        let (result, diagnostics) = self.infer_prog_partial(groups);
        // Return the first error diagnostic (skip warnings like UnresolvedName).
        for diag in diagnostics {
            if !matches!(
                diag.kind,
                crate::diagnostic::TixDiagnosticKind::UnresolvedName { .. }
            ) {
                return Err(diag);
            }
        }
        Ok(result)
    }

    /// Inference entry point that always produces an InferenceResult, even when
    /// errors occur. Errors are collected rather than short-circuiting — SCC
    /// groups after a failed one still get inferred, so the LSP can show types
    /// for successfully-inferred bindings alongside error diagnostics.
    pub fn infer_prog_partial(
        mut self,
        groups: GroupedDefs,
    ) -> (InferenceResult, Vec<TixDiagnostic>) {
        // Pre-allocate TyIds for all names and expressions so they can be
        // referenced before they are inferred (needed for recursive definitions).
        let len = self.module.names().len() + self.module.exprs().len();
        for _ in 0..len {
            self.new_var();
        }

        let mut errors = Vec::new();

        for group in groups {
            if let Some(err) = self.infer_scc_group(group) {
                errors.push(err);
            }
        }

        if let Err(err) = self.infer_root() {
            errors.push(err);
        }

        // Convert internal errors and warnings to display-ready diagnostics
        // while we still have access to the TypeStorage for canonicalization.
        let warnings = std::mem::take(&mut self.warnings);
        let mut diagnostics =
            diagnostic::errors_to_diagnostics(&errors, &self.table, &self.alias_provenance);
        diagnostics.extend(diagnostic::warnings_to_diagnostics(&warnings));

        let mut collector = Collector::new(self);
        let result = collector.finalize_inference();
        (result, diagnostics)
    }

    fn infer_root(&mut self) -> Result<(), LocatedError> {
        self.infer_expr(self.module.entry_expr)?;
        self.resolve_pending()?;
        Ok(())
    }

    /// Infer an SCC group, returning any error that occurred. Cleanup (level
    /// exit, deferred overload bookkeeping, poly_type_env updates) always runs
    /// regardless of whether inference succeeded — this prevents level counter
    /// imbalance and ensures successfully-inferred names within the group are
    /// still recorded.
    fn infer_scc_group(&mut self, group: DependentGroup) -> Option<LocatedError> {
        self.table.enter_level();

        // Lift pre-allocated name vars to the current (inner) level so that
        // type variables created during inference of this group are at the
        // right level for generalization.
        for def in &group {
            let name_ty = self.ty_for_name_direct(def.name());
            self.table.set_var_level(name_ty, self.table.current_level);
        }

        let (inferred, error) = self.infer_scc_group_inner(&group);

        // --- Cleanup always runs, even on error ---

        // Move unresolved overloads to deferred list — they'll be re-instantiated
        // per call-site during extrusion.
        let remaining = std::mem::take(&mut self.deferred.overloads);
        self.deferred.deferred_overloads.extend(remaining);

        // Snapshot each successfully-inferred name's canonical type NOW, before
        // exit_level and before use-site extrusions add concrete bounds.
        for &(name_id, ty) in &inferred {
            let poly_ty = self.resolve_to_concrete_id(ty).unwrap_or(ty);
            let output =
                canonicalize_standalone(&self.table, &self.alias_provenance, poly_ty, true);
            let simplified = simplify(&output);
            self.early_canonical.insert(name_id, simplified);
        }

        self.table.exit_level();

        // Record the inferred type in poly_type_env for successfully-inferred
        // names, resolving Variables to their concrete type where possible.
        for (name_id, ty) in inferred {
            if self.poly_type_env.contains_idx(name_id) {
                continue;
            }
            let poly_ty = self.resolve_to_concrete_id(ty).unwrap_or(ty);
            self.poly_type_env.insert(name_id, poly_ty);
        }

        error
    }

    /// Fallible inner logic for SCC group inference. Returns the successfully-
    /// inferred (name, ty) pairs and an optional error. Inference stops at the
    /// first error within the group, but names inferred before that point are
    /// still returned.
    fn infer_scc_group_inner(
        &mut self,
        group: &DependentGroup,
    ) -> (Vec<(lang_ast::NameId, TyId)>, Option<LocatedError>) {
        let mut inferred: Vec<(lang_ast::NameId, TyId)> = Vec::new();

        for def in group {
            let ty = match self.infer_expr(def.expr()) {
                Ok(ty) => ty,
                Err(err) => return (inferred, Some(err)),
            };
            let name_id = def.name();

            // Link the pre-allocated name slot to the inferred type.
            let name_slot = self.ty_for_name_direct(name_id);
            if let Err(err) = self
                .constrain(ty, name_slot)
                .map_err(|e| self.locate_err(e))
            {
                return (inferred, Some(err));
            }
            if let Err(err) = self
                .constrain(name_slot, ty)
                .map_err(|e| self.locate_err(e))
            {
                return (inferred, Some(err));
            }

            // Check for type annotations in doc comments.
            if let Err(err) = self.apply_type_annotation(name_id, ty) {
                return (inferred, Some(err));
            }

            inferred.push((name_id, ty));
        }

        // Resolve pending overload and merge constraints now that we have
        // type information from the entire SCC group.
        if let Err(err) = self.resolve_pending() {
            return (inferred, Some(err));
        }

        (inferred, None)
    }

    // ==========================================================================
    // Extrude — SimpleSub's replacement for instantiation
    // ==========================================================================
    //
    // When referencing a polymorphic name, we "extrude" its type to the current
    // level. Variables at a deeper level get fresh copies at the current level,
    // with appropriate subtyping constraints linking them to the original.
    // The `polarity` parameter tracks variance: positive = output/covariant,
    // negative = input/contravariant.

    pub fn extrude(&mut self, ty_id: TyId, polarity: bool) -> TyId {
        let mut cache = HashMap::new();
        let result = self.extrude_inner(ty_id, polarity, &mut cache);

        // Re-instantiate deferred overloads for any vars that were extruded.
        // This creates per-call-site overload constraints with the fresh vars.
        //
        // NOTE: This fixed-point loop is O(n²) in the worst case (n deferred
        // overloads where each pass resolves one). A worklist approach — only
        // re-checking overloads whose operands were just added to the cache —
        // would be O(n). Not a concern for typical Nix code, but worth
        // revisiting if profiling shows extrude as a bottleneck.
        //
        // When at least one operand of a deferred overload was extruded, we need
        // a fresh copy of the entire overload for this call site. For operand
        // vars already in the extrude cache (at either polarity), we use the
        // cached fresh copy. For operand vars NOT in the cache (e.g. Select
        // result vars connected only via bounds, not via structural type), we
        // extrude them explicitly to create per-call-site copies.
        //
        // We use a fixed-point loop because extruding one overload's operands
        // may add new entries to the cache, which then makes other overloads
        // eligible for re-instantiation (e.g. when overload chains share
        // intermediate result vars like `(a + b) + (c + d)`).
        let deferred = self.deferred.deferred_overloads.clone();
        let mut processed = vec![false; deferred.len()];
        loop {
            let mut made_progress = false;

            for (i, ov) in deferred.iter().enumerate() {
                if processed[i] {
                    continue;
                }

                let any_extruded = cache.contains_key(&ov.constraint.lhs)
                    || cache.contains_key(&ov.constraint.rhs)
                    || cache.contains_key(&ov.constraint.ret);

                if any_extruded {
                    // For each operand, use the cached fresh var if available,
                    // otherwise extrude it now in positive polarity.
                    let get_or_extrude =
                        |id: TyId, this: &mut Self, cache: &mut HashMap<TyId, TyId>| -> TyId {
                            if let Some(&fresh) = cache.get(&id) {
                                fresh
                            } else {
                                this.extrude_inner(id, true, cache)
                            }
                        };

                    let new_lhs = get_or_extrude(ov.constraint.lhs, self, &mut cache);
                    let new_rhs = get_or_extrude(ov.constraint.rhs, self, &mut cache);
                    let new_ret = get_or_extrude(ov.constraint.ret, self, &mut cache);

                    self.deferred.overloads.push(PendingOverload {
                        op: ov.op,
                        constraint: BinConstraint {
                            lhs: new_lhs,
                            rhs: new_rhs,
                            ret: new_ret,
                        },
                    });

                    processed[i] = true;
                    made_progress = true;
                }
            }

            if !made_progress {
                break;
            }
        }

        result
    }

    fn extrude_inner(
        &mut self,
        ty_id: TyId,
        polarity: bool,
        cache: &mut HashMap<TyId, TyId>,
    ) -> TyId {
        if let Some(&cached) = cache.get(&ty_id) {
            return cached;
        }

        let entry = self.table.get(ty_id).clone();

        match entry {
            TypeEntry::Variable(ref v) if v.level >= self.table.current_level => {
                // This variable was bound at a deeper level — it's polymorphic.
                // However, if it has been pinned to a concrete type (has the same
                // concrete type as both a direct lower and upper bound), it was
                // fully resolved by e.g. overload resolution. Extrude the concrete
                // type instead of creating a fresh variable, to avoid losing the
                // resolved type information.
                if let Some(pinned) = self.find_pinned_concrete(v) {
                    // Insert into cache so deferred overload re-instantiation
                    // can find this var was extruded.
                    let concrete_id = self.alloc_concrete(pinned);
                    let result = self.extrude_inner(concrete_id, polarity, cache);
                    cache.insert(ty_id, result);
                    return result;
                }

                // Truly polymorphic — create a fresh variable at the current level.
                //
                // Per the SimpleSub paper, we link fresh vars to originals via
                // direct bounds manipulation rather than constrain(). Using
                // constrain() would propagate bounds bidirectionally, allowing
                // use-site constraints on the fresh var to leak back to the
                // original polymorphic variable and contaminate subsequent
                // extrusions.
                let fresh = self.new_var();
                cache.insert(ty_id, fresh);

                if polarity {
                    // Positive position: original <: fresh (one-way link).
                    // Copy original's lower bounds (extruded) into fresh.
                    self.table.add_upper_bound(ty_id, fresh);
                    let lower_bounds = v.lower_bounds.clone();
                    for lb in lower_bounds {
                        let extruded_lb = self.extrude_inner(lb, polarity, cache);
                        self.table.add_lower_bound(fresh, extruded_lb);
                    }
                } else {
                    // Negative position: fresh <: original (one-way link).
                    // Copy original's upper bounds (extruded) into fresh.
                    self.table.add_lower_bound(ty_id, fresh);
                    let upper_bounds = v.upper_bounds.clone();
                    for ub in upper_bounds {
                        let extruded_ub = self.extrude_inner(ub, polarity, cache);
                        self.table.add_upper_bound(fresh, extruded_ub);
                    }
                }
                fresh
            }
            TypeEntry::Variable(_) => {
                // Variable at current level or shallower — not polymorphic, return as-is.
                ty_id
            }
            TypeEntry::Concrete(ty) => {
                let result = match ty {
                    Ty::Lambda { param, body } => {
                        // Insert a placeholder to handle recursive types.
                        let placeholder = self.new_var();
                        cache.insert(ty_id, placeholder);

                        let p = self.extrude_inner(param, !polarity, cache); // flip polarity
                        let b = self.extrude_inner(body, polarity, cache);
                        let result = self.alloc_concrete(Ty::Lambda { param: p, body: b });

                        // Link placeholder to result.
                        self.constrain(result, placeholder).expect("extrude link");
                        self.constrain(placeholder, result).expect("extrude link");

                        result
                    }
                    Ty::List(elem) => {
                        let e = self.extrude_inner(elem, polarity, cache);
                        self.alloc_concrete(Ty::List(e))
                    }
                    Ty::AttrSet(attr) => {
                        let new_fields = attr
                            .fields
                            .iter()
                            .map(|(k, &v)| (k.clone(), self.extrude_inner(v, polarity, cache)))
                            .collect();
                        let new_dyn = attr.dyn_ty.map(|d| self.extrude_inner(d, polarity, cache));
                        self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                            fields: new_fields,
                            dyn_ty: new_dyn,
                            open: attr.open,
                        }))
                    }
                    Ty::Primitive(_) => ty_id,
                    Ty::TyVar(_) => ty_id,
                };

                // Propagate alias provenance through extrusion so that
                // references to aliased types preserve the alias name.
                if let Some(name) = self.alias_provenance.get(&ty_id).cloned() {
                    self.alias_provenance.insert(result, name);
                }

                result
            }
        }
    }

    // ==========================================================================
    // Pending constraint resolution
    // ==========================================================================
    //
    // After inferring an SCC group or the root, we resolve pending overload
    // and merge constraints. These are deferred because they need both operand
    // types to be at least partially known.

    fn resolve_pending(&mut self) -> Result<(), LocatedError> {
        // Fixed-point loop: keep trying until no more progress.
        loop {
            let mut made_progress = false;

            // Resolve overloads.
            let overloads = std::mem::take(&mut self.deferred.overloads);
            let mut remaining_overloads = Vec::new();
            for ov in overloads {
                match self
                    .try_resolve_overload(&ov)
                    .map_err(|err| self.locate_err(err))?
                {
                    OverloadProgress::FullyResolved => made_progress = true,
                    OverloadProgress::PartialProgress => {
                        // Partial work was done (constraints added) but the
                        // overload isn't fully resolved yet. Keep it pending
                        // and mark progress so the loop iterates again.
                        made_progress = true;
                        remaining_overloads.push(ov);
                    }
                    OverloadProgress::NoProgress => remaining_overloads.push(ov),
                }
            }
            self.deferred.overloads = remaining_overloads;

            // Resolve merges.
            let merges = std::mem::take(&mut self.deferred.merges);
            let mut remaining_merges = Vec::new();
            for mg in merges {
                match self
                    .try_resolve_merge(&mg)
                    .map_err(|err| self.locate_err(err))?
                {
                    true => made_progress = true,
                    false => remaining_merges.push(mg),
                }
            }
            self.deferred.merges = remaining_merges;

            if !made_progress {
                break;
            }
        }

        Ok(())
    }

    fn try_resolve_overload(
        &mut self,
        ov: &PendingOverload,
    ) -> Result<OverloadProgress, InferenceError> {
        let c = &ov.constraint;
        let lhs_concrete = self.find_concrete(c.lhs);
        let rhs_concrete = self.find_concrete(c.rhs);

        // ---- Phase 1: Full Resolution — both operands concrete ----

        if let (Some(lhs_ty), Some(rhs_ty)) = (&lhs_concrete, &rhs_concrete) {
            let ret_ty = self
                .solve_bin_op_types(ov.op, lhs_ty, rhs_ty)
                .ok_or_else(|| {
                    InferenceError::InvalidBinOp(ov.op, lhs_ty.clone(), rhs_ty.clone())
                })?;

            let ret_id = self.alloc_concrete(ret_ty);
            self.constrain(ret_id, c.ret)?;
            self.constrain(c.ret, ret_id)?;
            return Ok(OverloadProgress::FullyResolved);
        }

        // ---- Phase 2: Partial Resolution — at least one operand unknown ----
        //
        // Track the constrain_cache size so we can detect whether partial
        // resolution actually added new constraints. If the cache didn't grow,
        // the constraints were all redundant and re-iterating would produce an
        // infinite loop.
        let cache_size_before = self.constrain_cache.len();

        // --- 2a: Numeric operand → constrain unknown side to Number ---
        //
        // When one operand is a known numeric type, bound the unknown side and
        // result by Number. This gives e.g. `add 1` → `number -> number`
        // instead of `a -> b`.
        let lhs_numeric = lhs_concrete
            .as_ref()
            .is_some_and(|t| matches!(t, Ty::Primitive(p) if p.is_number()));
        let rhs_numeric = rhs_concrete
            .as_ref()
            .is_some_and(|t| matches!(t, Ty::Primitive(p) if p.is_number()));

        if lhs_numeric || rhs_numeric {
            let number = self.alloc_prim(PrimitiveTy::Number);
            // Only constrain the unknown side — the known side is already concrete.
            if lhs_numeric && rhs_concrete.is_none() {
                self.constrain(c.rhs, number)?;
            }
            if rhs_numeric && lhs_concrete.is_none() {
                self.constrain(c.lhs, number)?;
            }
            // Result bounded above by Number. We only add upper bound (not lower)
            // so that later full resolution can pin to a more specific type like Int.
            self.constrain(c.ret, number)?;
        }

        // --- 2b: String/path lhs with + → pin return type ---
        //
        // In Nix, the return type of `+` is always the lhs type when lhs is
        // string or path. We can pin ret early without waiting for the rhs.
        if ov.op.is_add() {
            let lhs_is_string = matches!(&lhs_concrete, Some(Ty::Primitive(PrimitiveTy::String)));
            let lhs_is_path = matches!(&lhs_concrete, Some(Ty::Primitive(PrimitiveTy::Path)));

            if lhs_is_string || lhs_is_path {
                let ret_prim = if lhs_is_string {
                    PrimitiveTy::String
                } else {
                    PrimitiveTy::Path
                };
                let ret_id = self.alloc_prim(ret_prim);
                self.constrain(ret_id, c.ret)?;
                self.constrain(c.ret, ret_id)?;
            }
        }

        // ---- Progress detection ----
        //
        // If no new constraints were added, report NoProgress to prevent
        // infinite re-iteration of the deferred overload loop.
        if self.constrain_cache.len() > cache_size_before {
            Ok(OverloadProgress::PartialProgress)
        } else {
            Ok(OverloadProgress::NoProgress)
        }
    }

    fn try_resolve_merge(&mut self, mg: &PendingMerge) -> Result<bool, InferenceError> {
        let lhs_concrete = self.find_concrete(mg.lhs);
        let rhs_concrete = self.find_concrete(mg.rhs);

        match (&lhs_concrete, &rhs_concrete) {
            (Some(Ty::AttrSet(_)), Some(Ty::AttrSet(_))) => {}
            (Some(lhs), Some(rhs)) => {
                return Err(InferenceError::InvalidAttrMerge(lhs.clone(), rhs.clone()));
            }
            _ => return Ok(false),
        }
        // Both are AttrSets — safe to destructure after the guard above.
        let (Some(Ty::AttrSet(lhs_attr)), Some(Ty::AttrSet(rhs_attr))) =
            (lhs_concrete, rhs_concrete)
        else {
            unreachable!()
        };

        let merged = lhs_attr.clone().merge(rhs_attr.clone());
        let merged_id = self.alloc_concrete(Ty::AttrSet(merged));
        self.constrain(merged_id, mg.ret)?;
        self.constrain(mg.ret, merged_id)?;
        Ok(true)
    }

    /// Check if a variable has been pinned to a simple concrete type — i.e. the
    /// same primitive type appears as both a direct lower and upper bound. This
    /// indicates the variable was fully resolved (e.g. by overload resolution) and
    /// is no longer truly polymorphic.
    ///
    /// Only primitives are considered "pinned" — types with internal structure
    /// (Lambda, List, AttrSet) may contain polymorphic sub-components that need
    /// proper extrusion.
    fn find_pinned_concrete(&self, v: &crate::storage::TypeVariable) -> Option<Ty<TyId>> {
        // Collect primitive types from direct lower bounds.
        let lower_prims: Vec<_> = v
            .lower_bounds
            .iter()
            .filter_map(|&lb| {
                if let TypeEntry::Concrete(ty @ Ty::Primitive(_)) = self.table.get(lb) {
                    Some(ty.clone())
                } else {
                    None
                }
            })
            .collect();

        // Check if any of those also appear as a direct upper bound.
        for &ub in &v.upper_bounds {
            if let TypeEntry::Concrete(ub_ty @ Ty::Primitive(_)) = self.table.get(ub) {
                if lower_prims.contains(ub_ty) {
                    return Some(ub_ty.clone());
                }
            }
        }
        None
    }

    /// Walk lower bounds transitively to find a Concrete entry and return its
    /// TyId. Used to resolve partial-application result variables (which point
    /// to a Lambda via lower bounds) so poly_type_env stores the structural type
    /// that extrude can traverse.
    fn resolve_to_concrete_id(&self, ty_id: TyId) -> Option<TyId> {
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
        match self.table.get(ty_id) {
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
    pub(crate) fn find_concrete(&self, ty_id: TyId) -> Option<Ty<TyId>> {
        let mut visited = HashSet::new();
        self.find_concrete_inner(ty_id, &mut visited)
    }

    fn find_concrete_inner(&self, ty_id: TyId, visited: &mut HashSet<TyId>) -> Option<Ty<TyId>> {
        if !visited.insert(ty_id) {
            return None; // Cycle detected — stop recursing.
        }
        match self.table.get(ty_id) {
            TypeEntry::Concrete(ty) => Some(ty.clone()),
            TypeEntry::Variable(v) => {
                // Check lower bounds for a concrete type.
                let bounds = v.lower_bounds.clone();
                for lb in bounds {
                    if let Some(ty) = self.find_concrete_inner(lb, visited) {
                        return Some(ty);
                    }
                }
                None
            }
        }
    }

    fn solve_bin_op_types(
        &self,
        op: OverloadBinOp,
        lhs: &Ty<TyId>,
        rhs: &Ty<TyId>,
    ) -> Option<Ty<TyId>> {
        use Ty::Primitive;

        let (Primitive(l), Primitive(r)) = (lhs, rhs) else {
            return None;
        };

        // Both numbers — float wins, Number stays Number.
        if l.is_number() && r.is_number() {
            if l.is_float() || r.is_float() {
                return Some(Primitive(PrimitiveTy::Float));
            }
            if matches!(l, PrimitiveTy::Number) || matches!(r, PrimitiveTy::Number) {
                return Some(Primitive(PrimitiveTy::Number));
            }
            return Some(lhs.clone()); // both Int
        }

        if !op.is_add() {
            return None;
        }

        // Both addable (strings/paths) — lhs type wins.
        if l.is_addable() && r.is_addable() {
            Some(lhs.clone())
        } else {
            None
        }
    }
}
