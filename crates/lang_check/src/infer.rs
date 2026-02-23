// ==============================================================================
// Inference Orchestration — SCC groups, generalization, extrude
// ==============================================================================
//
// This module drives the overall inference process: iterating over SCC groups,
// inferring each definition, resolving pending constraints, and generalizing
// type variables via SimpleSub's level-based approach (extrude).

use std::collections::HashMap;

use super::{CheckCtx, InferenceError, InferenceResult, LocatedError, Polarity, TyId};
use crate::collect::{canonicalize_standalone, Collector};
use crate::diagnostic;
use crate::diagnostic::TixDiagnostic;
use crate::infer_expr::{BinConstraint, PendingHasField, PendingMerge, PendingOverload};
use crate::storage::TypeEntry;
use lang_ast::nameres::{DependentGroup, GroupedDefs};
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
    pub fn infer_prog(self, groups: GroupedDefs) -> Result<InferenceResult, Box<TixDiagnostic>> {
        let (result, diagnostics) = self.infer_prog_partial(groups);
        // Return the first error diagnostic (skip warnings like UnresolvedName).
        for diag in diagnostics {
            if !matches!(
                diag.kind,
                crate::diagnostic::TixDiagnosticKind::UnresolvedName { .. }
                    | crate::diagnostic::TixDiagnosticKind::AnnotationArityMismatch { .. }
                    | crate::diagnostic::TixDiagnosticKind::AnnotationUnchecked { .. }
            ) {
                return Err(Box::new(diag));
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
            diagnostic::errors_to_diagnostics(&errors, &self.types.storage, &self.alias_provenance);
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
        self.types.storage.enter_level();

        // Lift pre-allocated name vars to the current (inner) level so that
        // type variables created during inference of this group are at the
        // right level for generalization.
        for def in &group {
            let name_ty = self.ty_for_name_direct(def.name());
            self.types
                .storage
                .set_var_level(name_ty, self.types.storage.current_level);
        }

        // Also lift pre-allocated expression slots for all sub-expressions
        // within this group's definitions. Without this, expression slots
        // remain at level 0 and aren't extruded during instantiation,
        // creating a back-channel through which use-site constraints leak
        // back to the original polymorphic type variables.
        for def in &group {
            self.lift_expr_slots(def.expr());
        }

        let (inferred, error) = self.infer_scc_group_inner(&group);

        // --- Cleanup always runs, even on error ---

        // Move unresolved overloads to the carried list — they'll be
        // re-instantiated per call-site during extrusion.
        let remaining = std::mem::take(&mut self.deferred.active);
        for constraint in remaining {
            if let super::PendingConstraint::Overload(ov) = constraint {
                self.deferred.carried.push(ov);
            }
            // Merges and HasField constraints are discarded here — they're
            // only relevant within their SCC group. (Constraints that couldn't
            // resolve within the group remain unresolved, matching the
            // previous behavior.)
        }

        // Snapshot each successfully-inferred name's canonical type NOW, before
        // exit_level and before use-site extrusions add concrete bounds.
        for &(name_id, ty) in &inferred {
            let poly_ty = self.types.resolve_to_concrete_id(ty).unwrap_or(ty);
            let output = canonicalize_standalone(
                &self.types.storage,
                &self.alias_provenance,
                poly_ty,
                Polarity::Positive,
            );
            let simplified = simplify(&output);
            self.early_canonical.insert(name_id, simplified);
        }

        self.types.storage.exit_level();

        // Record the inferred type in poly_type_env for successfully-inferred
        // names, resolving Variables to their concrete type where possible.
        //
        // Only resolve to a concrete type when the variable has a SINGLE
        // concrete lower bound. A variable with multiple concrete lower bounds
        // represents a union type (e.g. `null | int`), and resolving to just
        // one member would lose the union semantics. This matters for type
        // narrowing: `if x == null then ... else x + 1` needs the variable
        // to contain both null and int so that narrowing can exclude null.
        for (name_id, ty) in inferred {
            if self.poly_type_env.contains_idx(name_id) {
                continue;
            }
            let poly_ty = self.types.resolve_to_concrete_id(ty).unwrap_or(ty);
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
            // If this binding sits inside a narrowing scope (detected during
            // SCC grouping in lang_ast), install the narrowing overrides so
            // that references to narrowed names (e.g. `pasta` after
            // `pasta != null`) get the narrowed type instead of the original.
            let narrow_scope = def.narrow_scope();
            let saved = if !narrow_scope.is_empty() {
                self.install_narrow_overrides(narrow_scope)
            } else {
                Vec::new()
            };

            let ty = match self.infer_expr(def.expr()) {
                Ok(ty) => {
                    self.restore_narrow_overrides(saved);
                    ty
                }
                Err(err) => {
                    self.restore_narrow_overrides(saved);
                    return (inferred, Some(err));
                }
            };
            let name_id = def.name();

            // Link the pre-allocated name slot to the inferred type.
            let name_slot = self.ty_for_name_direct(name_id);
            if let Err(err) = self.constrain_equal(ty, name_slot) {
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

    pub fn extrude(&mut self, ty_id: TyId, polarity: Polarity) -> TyId {
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
        let deferred = self.deferred.carried.clone();
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
                                this.extrude_inner(id, Polarity::Positive, cache)
                            }
                        };

                    let new_lhs = get_or_extrude(ov.constraint.lhs, self, &mut cache);
                    let new_rhs = get_or_extrude(ov.constraint.rhs, self, &mut cache);
                    let new_ret = get_or_extrude(ov.constraint.ret, self, &mut cache);

                    self.deferred
                        .active
                        .push(super::PendingConstraint::Overload(PendingOverload {
                            op: ov.op,
                            constraint: BinConstraint {
                                lhs: new_lhs,
                                rhs: new_rhs,
                                ret: new_ret,
                                at_expr: ov.constraint.at_expr,
                            },
                        }));

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
        polarity: Polarity,
        cache: &mut HashMap<TyId, TyId>,
    ) -> TyId {
        if let Some(&cached) = cache.get(&ty_id) {
            return cached;
        }

        let entry = self.types.storage.get(ty_id).clone();

        match entry {
            TypeEntry::Variable(ref v) if v.level >= self.types.storage.current_level => {
                // This variable was bound at a deeper level — it's polymorphic.
                // However, if it has been pinned to a concrete type (has the same
                // concrete type as both a direct lower and upper bound), it was
                // fully resolved by e.g. overload resolution. Extrude the concrete
                // type instead of creating a fresh variable, to avoid losing the
                // resolved type information.
                if let Some(pinned) = self.types.find_pinned_concrete(v) {
                    // Insert into cache so deferred overload re-instantiation
                    // can find this var was extruded.
                    let concrete_id = self.alloc_concrete(pinned);
                    let result = self.extrude_inner(concrete_id, polarity, cache);
                    cache.insert(ty_id, result);
                    return result;
                }

                // Truly polymorphic — create a fresh variable at the current level.
                let fresh = self.new_var();
                cache.insert(ty_id, fresh);
                self.link_extruded_var(ty_id, fresh, polarity, v.clone(), cache);
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

                        let p = self.extrude_inner(param, polarity.flip(), cache); // flip polarity
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
                            optional_fields: attr.optional_fields.clone(),
                        }))
                    }
                    Ty::Primitive(_) => ty_id,
                    Ty::TyVar(_) => ty_id,
                    // Negation flips polarity, same as Lambda param.
                    Ty::Neg(inner) => {
                        let e = self.extrude_inner(inner, polarity.flip(), cache);
                        self.alloc_concrete(Ty::Neg(e))
                    }
                    // Intersection and Union: covariant — polarity preserved.
                    // This is what makes narrowing survive generalization:
                    // Inter(α, ¬T) extrudes to Inter(α', ¬T') where α' is
                    // the fresh call-site copy.
                    Ty::Inter(a, b) => {
                        let ea = self.extrude_inner(a, polarity, cache);
                        let eb = self.extrude_inner(b, polarity, cache);
                        self.alloc_concrete(Ty::Inter(ea, eb))
                    }
                    Ty::Union(a, b) => {
                        let ea = self.extrude_inner(a, polarity, cache);
                        let eb = self.extrude_inner(b, polarity, cache);
                        self.alloc_concrete(Ty::Union(ea, eb))
                    }
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

    /// Link a freshly extruded variable to the original polymorphic variable.
    ///
    /// Per the SimpleSub paper, we use direct bounds manipulation rather than
    /// constrain(). Using constrain() would propagate bounds bidirectionally,
    /// allowing use-site constraints on the fresh var to leak back to the
    /// original polymorphic variable and contaminate subsequent extrusions.
    ///
    /// Polarity determines the direction of the link and which bounds to copy:
    /// - Positive: original <: fresh, copy lower bounds into fresh
    /// - Negative: fresh <: original, copy upper bounds into fresh
    fn link_extruded_var(
        &mut self,
        original: TyId,
        fresh: TyId,
        polarity: Polarity,
        var: crate::storage::TypeVariable,
        cache: &mut HashMap<TyId, TyId>,
    ) {
        // In positive position, `original <: fresh`: the original flows into
        // the fresh var. We install the link as an upper bound on original and
        // copy the original's lower bounds (extruded) into fresh.
        //
        // In negative position, `fresh <: original`: symmetrically reversed.
        let bounds_to_copy = match polarity {
            Polarity::Positive => {
                self.types.storage.add_upper_bound(original, fresh);
                var.lower_bounds.clone()
            }
            Polarity::Negative => {
                self.types.storage.add_lower_bound(original, fresh);
                var.upper_bounds.clone()
            }
        };

        for bound in bounds_to_copy {
            let extruded = self.extrude_inner(bound, polarity, cache);
            match polarity {
                Polarity::Positive => self.types.storage.add_lower_bound(fresh, extruded),
                Polarity::Negative => self.types.storage.add_upper_bound(fresh, extruded),
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

            let pending = std::mem::take(&mut self.deferred.active);
            let mut remaining = Vec::new();

            for constraint in pending {
                match constraint {
                    super::PendingConstraint::Overload(ov) => {
                        self.current_expr = ov.constraint.at_expr;
                        match self
                            .try_resolve_overload(&ov)
                            .map_err(|err| self.locate_err(err))?
                        {
                            OverloadProgress::FullyResolved => made_progress = true,
                            OverloadProgress::PartialProgress => {
                                made_progress = true;
                                remaining.push(super::PendingConstraint::Overload(ov));
                            }
                            OverloadProgress::NoProgress => {
                                remaining.push(super::PendingConstraint::Overload(ov));
                            }
                        }
                    }
                    super::PendingConstraint::Merge(mg) => {
                        self.current_expr = mg.at_expr;
                        match self
                            .try_resolve_merge(&mg)
                            .map_err(|err| self.locate_err(err))?
                        {
                            true => made_progress = true,
                            false => remaining.push(super::PendingConstraint::Merge(mg)),
                        }
                    }
                    super::PendingConstraint::HasField(hf) => {
                        self.current_expr = hf.at_expr;
                        match self
                            .try_resolve_has_field(&hf)
                            .map_err(|err| self.locate_err(err))?
                        {
                            true => made_progress = true,
                            false => remaining.push(super::PendingConstraint::HasField(hf)),
                        }
                    }
                }
            }

            self.deferred.active = remaining;

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
        let spec = crate::operators::overload_spec(ov.op);
        // Use find_concrete_through_inter so narrowed types like
        // Inter(α, Int) are visible to the overload resolver as Int.
        let lhs_concrete = self.types.find_concrete_through_inter(c.lhs);
        let rhs_concrete = self.types.find_concrete_through_inter(c.rhs);

        // ---- Phase 1: Full Resolution — both operands concrete ----

        if let (Some(lhs_ty), Some(rhs_ty)) = (&lhs_concrete, &rhs_concrete) {
            let (Ty::Primitive(l), Ty::Primitive(r)) = (lhs_ty, rhs_ty) else {
                return Err(InferenceError::InvalidBinOp(Box::new((
                    ov.op,
                    lhs_ty.clone(),
                    rhs_ty.clone(),
                ))));
            };
            let ret_prim = (spec.full_resolve)(l, r).ok_or_else(|| {
                InferenceError::InvalidBinOp(Box::new((ov.op, lhs_ty.clone(), rhs_ty.clone())))
            })?;

            let ret_id = self.alloc_prim(ret_prim);
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
        let cache_size_before = self.types.constrain_cache.len();

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

        // --- 2b: Known lhs type → pin return type early ---
        //
        // Use the spec's early_ret_from_lhs to check if the lhs type alone
        // determines the return type (e.g. string + _ → string, path + _ → path).
        if let Some(Ty::Primitive(lhs_prim)) = &lhs_concrete {
            if let Some(ret_prim) = (spec.early_ret_from_lhs)(lhs_prim) {
                let ret_id = self.alloc_prim(ret_prim);
                self.constrain(ret_id, c.ret)?;
                self.constrain(c.ret, ret_id)?;
            }
        }

        // ---- Progress detection ----
        //
        // If no new constraints were added, report NoProgress to prevent
        // infinite re-iteration of the deferred overload loop.
        if self.types.constrain_cache.len() > cache_size_before {
            Ok(OverloadProgress::PartialProgress)
        } else {
            Ok(OverloadProgress::NoProgress)
        }
    }

    /// Try to resolve a deferred has-field constraint.
    ///
    /// Returns Ok(true) if resolved (field found, or type is non-attrset meaning
    /// a TypeMismatch was already reported by the original constrain call).
    /// Returns Ok(false) if still pending (set type not yet concrete, or still open).
    /// Returns Err if the set resolved to a closed attrset without the field.
    fn try_resolve_has_field(&mut self, hf: &PendingHasField) -> Result<bool, InferenceError> {
        // Use find_concrete_through_inter so narrowed types like
        // Inter(α, {field: β}) expose the attrset for field lookup.
        let Some(concrete) = self.types.find_concrete_through_inter(hf.set_ty) else {
            return Ok(false); // not yet concrete
        };

        match concrete {
            Ty::AttrSet(attr) => {
                if let Some(&actual_field_ty) = attr.fields.get(&hf.field) {
                    // Field found — link the types. This is likely redundant with
                    // the existing constrain() from Select, but harmless (the
                    // constrain_cache deduplicates).
                    self.constrain(actual_field_ty, hf.field_ty)?;
                    Ok(true)
                } else if attr.dyn_ty.is_some() {
                    // Has a dynamic field type — the field might be satisfied
                    // by the dynamic portion. Keep pending.
                    // TODO: could constrain dyn_ty <: field_ty here.
                    Ok(false)
                } else if !attr.open {
                    // Closed attrset without the field.
                    Err(InferenceError::MissingField {
                        field: hf.field.clone(),
                        available: attr.fields.keys().cloned().collect(),
                    })
                } else {
                    // Still open — field might appear via future constraints.
                    Ok(false)
                }
            }
            // Non-attrset concrete type: the TypeMismatch (e.g. int vs attrset)
            // is already caught by the original constrain() in Select. Mark as
            // resolved to avoid double-reporting.
            _ => Ok(true),
        }
    }

    fn try_resolve_merge(&mut self, mg: &PendingMerge) -> Result<bool, InferenceError> {
        let lhs_concrete = self.types.find_concrete_through_inter(mg.lhs);
        let rhs_concrete = self.types.find_concrete_through_inter(mg.rhs);

        match (&lhs_concrete, &rhs_concrete) {
            (Some(Ty::AttrSet(_)), Some(Ty::AttrSet(_))) => {}
            (Some(lhs), Some(rhs)) => {
                return Err(InferenceError::InvalidAttrMerge(Box::new((
                    lhs.clone(),
                    rhs.clone(),
                ))));
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

    /// Recursively lift all pre-allocated expression TyId slots under `expr`
    /// to the current level. This ensures that during extrusion, these slots
    /// are treated as polymorphic and get fresh copies — preventing use-site
    /// constraints from leaking back through shared expression slots.
    fn lift_expr_slots(&mut self, expr: lang_ast::ExprId) {
        let slot = self.ty_for_expr(expr);
        self.types
            .storage
            .set_var_level(slot, self.types.storage.current_level);
        let e = self.module[expr].clone();
        e.walk_child_exprs(|child| self.lift_expr_slots(child));
    }
}
