// ==============================================================================
// Inference Orchestration — SCC groups, generalization, extrude
// ==============================================================================
//
// This module drives the overall inference process: iterating over SCC groups,
// inferring each definition, resolving pending constraints, and generalizing
// type variables via SimpleSub's level-based approach (extrude).

use std::sync::Arc;
use std::time::Instant;

/// Execute `$body`, measure wall-clock time, and run `$log` if elapsed exceeds
/// `$threshold_ms`. `$log` receives `$elapsed` as a `Duration` binding.
macro_rules! log_if_slow {
    ($threshold_ms:expr, $body:expr, |$elapsed:ident| $log:expr) => {{
        let __t = Instant::now();
        let __result = $body;
        let $elapsed = __t.elapsed();
        if $elapsed.as_millis() > $threshold_ms {
            $log;
        }
        __result
    }};
}

use rustc_hash::{FxHashMap, FxHashSet};

use super::{CheckCtx, InferenceError, InferenceResult, LocatedError, Polarity, TyId};
use crate::collect::{canonicalize_standalone, Collector};
use crate::diagnostic;
use crate::diagnostic::TixDiagnostic;
use crate::infer_expr::{
    BinConstraint, PendingHasField, PendingMerge, PendingOverload, PendingWithFallback,
};
use crate::storage::TypeEntry;
use lang_ast::nameres::{DependentGroup, GroupedDefs};
use lang_ast::Expr;
use lang_ty::simplify::simplify;
use lang_ty::{AttrSetTy, PrimitiveTy, Ty};

/// Read current process RSS from /proc/self/statm (Linux). Returns MB, or 0
/// on non-Linux platforms.
pub(crate) fn rss_mb() -> f64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok())
        .map(|pages| (pages * 4096) as f64 / (1024.0 * 1024.0))
        .unwrap_or(0.0)
}

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
        let (result, diagnostics, _timed_out) = self.infer_prog_partial(groups);
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
    ///
    /// Returns `(result, diagnostics, timed_out)` where `timed_out` is true
    /// when inference was aborted because the deadline was exceeded.
    pub fn infer_prog_partial(
        mut self,
        groups: GroupedDefs,
    ) -> (InferenceResult, Vec<TixDiagnostic>, bool) {
        // Pre-allocate TyIds for all names and expressions so they can be
        // referenced before they are inferred (needed for recursive definitions).
        let len = self.module.names().len() + self.module.exprs().len();
        for _ in 0..len {
            self.new_var();
        }

        let mut errors = Vec::new();

        // Pre-apply type annotations and context args on the entry Lambda's
        // pattern fields BEFORE SCC groups run. Without this, parameter types
        // (e.g. `lib :: Lib` from stubs) only flow in during infer_root()
        // which runs AFTER the SCC groups. That's too late: bindings like
        // `warnIf = lib.trivial.warnIf` would see an unconstrained `lib`
        // variable, and the stub's polymorphic types would only propagate
        // via plain constrain (not extrude), sharing type variables across
        // all call sites.
        if let Some(err) = self.pre_apply_entry_lambda_annotations() {
            errors.push(err);
        }

        let n_groups = groups.len();
        for (i, group) in groups.into_iter().enumerate() {
            // Check deadline before each SCC group so a single file can't
            // block the LSP indefinitely. Partial results (types inferred
            // so far) are still returned.
            if self.past_deadline() {
                log::warn!("inference deadline exceeded after {i}/{n_groups} SCC groups");
                break;
            }
            let group_names: Vec<_> = group
                .iter()
                .map(|d| self.module[d.name()].text.as_str().to_owned())
                .collect();
            let err = log_if_slow!(50, self.infer_scc_group(group), |elapsed| log::info!(
                "SCC group {i}/{n_groups} ({}) took {:.1}ms (slots: {}, RSS: {:.0}MB)",
                group_names.join(", "),
                elapsed.as_secs_f64() * 1000.0,
                self.types.storage.len(),
                rss_mb(),
            ));
            if let Some(err) = err {
                errors.push(err);
            }
        }

        if !self.past_deadline() {
            let root_err = log_if_slow!(10, self.infer_root(), |elapsed| log::info!(
                "infer_root took {:.1}ms (cache: {}, slots: {}, RSS: {:.0}MB)",
                elapsed.as_secs_f64() * 1000.0,
                self.types.constrain_cache.len(),
                self.types.storage.len(),
                rss_mb(),
            ));
            if let Err(err) = root_err {
                errors.push(err);
            }
        } else {
            log::warn!("skipping infer_root due to deadline");
        }

        // Convert internal errors and warnings to display-ready diagnostics
        // while we still have access to the TypeStorage for canonicalization.
        let warnings = std::mem::take(&mut self.warnings);
        let mut diagnostics = diagnostic::errors_to_diagnostics(&errors, &self.types.storage);
        diagnostics.extend(diagnostic::warnings_to_diagnostics(&warnings));

        // Capture before self is moved into Collector.
        let timed_out = self.past_deadline();

        let mut collector = Collector::new(self);
        let result = log_if_slow!(50, collector.finalize_inference(), |elapsed| log::info!(
            "canonicalization took {:.1}ms (RSS: {:.0}MB)",
            elapsed.as_secs_f64() * 1000.0,
            rss_mb(),
        ));
        (result, diagnostics, timed_out)
    }

    fn infer_root(&mut self) -> Result<(), LocatedError> {
        let expr_result = log_if_slow!(50, self.infer_expr(self.module.entry_expr), |elapsed| {
            log::info!(
                "infer_root: infer_expr {:.1}ms (cache: {}, slots: {})",
                elapsed.as_secs_f64() * 1000.0,
                self.types.constrain_cache.len(),
                self.types.storage.len(),
            );
        });
        expr_result?;
        log_if_slow!(50, self.resolve_pending()?, |elapsed| log::info!(
            "infer_root: resolve_pending {:.1}ms (cache: {}, slots: {})",
            elapsed.as_secs_f64() * 1000.0,
            self.types.constrain_cache.len(),
            self.types.storage.len(),
        ));
        Ok(())
    }

    /// Pre-apply type annotations and context args on the entry expression's
    /// Lambda pattern fields. This runs before SCC groups so that parameter
    /// types (e.g. `lib :: Lib` from stubs) are available when bindings like
    /// `warnIf = lib.trivial.warnIf` are inferred.
    ///
    /// Without this, the annotations only flow in during `infer_root()` (after
    /// all SCC groups), and the stub's polymorphic type variables propagate
    /// via plain `constrain` rather than `extrude`, causing all call sites to
    /// share the same type variables.
    fn pre_apply_entry_lambda_annotations(&mut self) -> Option<LocatedError> {
        let Expr::Lambda { pat: Some(pat), .. } = self.module[self.module.entry_expr].clone()
        else {
            return None;
        };

        // Determine effective context args: file-level context (tix.toml) or
        // doc comment context (/** context: nixos */) on the entry Lambda.
        let effective_context = if !self.context_args.is_empty() {
            Some(Arc::clone(&self.context_args))
        } else {
            self.resolve_doc_comment_context(self.module.entry_expr)
        };

        for &(name, _default_expr) in pat.fields.iter() {
            let Some(name) = name else { continue };
            let name_ty = self.ty_for_name_direct(name);

            // Apply doc comment type annotations (e.g. /** type: lib :: Lib */).
            if let Err(err) = self.apply_type_annotation(name, name_ty) {
                return Some(err);
            }

            // Apply context arg types (from tix.toml or /** context: <name> */).
            let field_text = self.module[name].text.clone();
            if let Some(ref ctx_args) = effective_context {
                if let Some(ctx_ty) = ctx_args.get(&field_text).cloned() {
                    let interned = self.intern_fresh_ty(ctx_ty);
                    if let Err(err) = self.constrain_equal(interned, name_ty) {
                        return Some(err);
                    }
                }
            }

            // Record this name so Lambda inference in infer_root() skips it.
            self.pre_annotated_params.insert(name);
        }

        None
    }

    /// Infer an SCC group, returning any error that occurred. Cleanup (level
    /// exit, deferred overload bookkeeping, poly_type_env updates) always runs
    /// regardless of whether inference succeeded — this prevents level counter
    /// imbalance and ensures successfully-inferred names within the group are
    /// still recorded.
    fn infer_scc_group(&mut self, group: DependentGroup) -> Option<LocatedError> {
        let scc_start = std::time::Instant::now();
        let scc_size = group.len();
        let cache_before = self.types.constrain_cache.len();
        let slots_before = self.types.storage.len();
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

        // Move unresolved overloads to the per-name carried map — they'll be
        // re-instantiated per call-site during extrusion of that name.
        let remaining = std::mem::take(&mut self.deferred.active);
        let group_names: Vec<lang_ast::NameId> = group.iter().map(|d| d.name()).collect();
        for constraint in remaining {
            if let super::PendingConstraint::Overload(ov) = constraint {
                if group_names.len() == 1 {
                    self.deferred
                        .carried
                        .entry(group_names[0])
                        .or_default()
                        .push(ov);
                } else {
                    // Mutual recursion: clone overloads to each name in the group
                    for &name_id in &group_names {
                        self.deferred
                            .carried
                            .entry(name_id)
                            .or_default()
                            .push(ov.clone());
                    }
                }
            }
            // Merges and HasField constraints are discarded here — they're
            // only relevant within their SCC group. (Constraints that couldn't
            // resolve within the group remain unresolved, matching the
            // previous behavior.)
        }

        // Snapshot each successfully-inferred name's canonical type NOW, before
        // exit_level and before use-site extrusions add concrete bounds.
        //
        // Canonicalize via name_slot (the pre-allocated variable for this name)
        // rather than poly_ty (the concrete inferred type), because name_slot
        // may have Named lower bounds from apply_type_annotation that aren't
        // visible on the concrete type itself.
        let canon_start = std::time::Instant::now();
        for &(name_id, _ty) in &inferred {
            let name_slot = self.ty_for_name_direct(name_id);
            let output =
                canonicalize_standalone(&self.types.storage, name_slot, Polarity::Positive);
            let simplified = simplify(&output);
            self.early_canonical.insert(name_id, simplified);
        }
        log::debug!(
            "  early canonicalization: {:.1}ms for {} names",
            canon_start.elapsed().as_secs_f64() * 1000.0,
            inferred.len(),
        );

        // Lift any sub-level variables in the type graph to the current SCC
        // level. Stub-interned variables (created at level 0 during annotation
        // processing) would otherwise be treated as non-polymorphic by extrusion,
        // causing all call sites to share the same type variables.
        for &(_, ty) in &inferred {
            self.lift_reachable_vars(ty);
        }

        self.compact_scc_graph(slots_before);

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
        let inferred_names: FxHashSet<_> = inferred.iter().map(|&(n, _)| n).collect();
        for (name_id, ty) in inferred {
            if self.poly_type_env.contains_idx(name_id) {
                continue;
            }
            let poly_ty = self.types.resolve_to_single_concrete_id(ty).unwrap_or(ty);

            // If the name slot has a Named lower bound (from type annotation),
            // wrap poly_ty in Named so that extrusion at usage sites preserves
            // the alias name (e.g. `Pkgs` instead of the structural attrset).
            let name_slot = self.ty_for_name_direct(name_id);
            let poly_ty = self.wrap_named_if_annotated(name_slot, poly_ty);

            self.poly_type_env.insert(name_id, poly_ty);
        }

        // Also record defs that FAILED inference, using their pre-allocated
        // name slot. Without this, `infer_bindings_to_attrset` (for `rec {}`)
        // would re-infer the failed def's body from scratch at root level,
        // triggering a massive cascade of extrusions and constraint propagation
        // (e.g. gvariant.nix's `mkValue` creates 580K+ type slots when
        // re-inferred because it extrudes every other poly function).
        if error.is_some() {
            for def in &group {
                let name_id = def.name();
                if !inferred_names.contains(&name_id) && !self.poly_type_env.contains_idx(name_id) {
                    let name_slot = self.ty_for_name_direct(name_id);
                    self.poly_type_env.insert(name_id, name_slot);
                }
            }
        }

        let scc_elapsed = scc_start.elapsed();
        log::info!(
            "SCC group: {} defs, {:.1}ms, cache {} → {}, slots {} → {}, carried overloads: {}",
            scc_size,
            scc_elapsed.as_secs_f64() * 1000.0,
            cache_before,
            self.types.constrain_cache.len(),
            slots_before,
            self.types.storage.len(),
            self.deferred
                .carried
                .values()
                .map(|v| v.len())
                .sum::<usize>(),
        );

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
        let infer_start = std::time::Instant::now();

        for def in group {
            if self.past_deadline() {
                break;
            }

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

            let def_start = std::time::Instant::now();
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
            log::debug!(
                "  def '{}': infer_expr {:.1}ms",
                self.module[name_id].text,
                def_start.elapsed().as_secs_f64() * 1000.0,
            );

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

        let infer_elapsed = infer_start.elapsed();
        log::debug!(
            "  all defs inferred in {:.1}ms, pending: {} active",
            infer_elapsed.as_secs_f64() * 1000.0,
            self.deferred.active.len(),
        );

        // Resolve pending overload and merge constraints now that we have
        // type information from the entire SCC group.
        let resolve_start = std::time::Instant::now();
        if let Err(err) = self.resolve_pending() {
            return (inferred, Some(err));
        }
        log::debug!(
            "  resolve_pending: {:.1}ms",
            resolve_start.elapsed().as_secs_f64() * 1000.0,
        );

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

    pub fn extrude(
        &mut self,
        ty_id: TyId,
        polarity: Polarity,
        name: Option<lang_ast::NameId>,
    ) -> TyId {
        let mut cache = FxHashMap::with_capacity_and_hasher(64, Default::default());
        let result = self.extrude_inner(ty_id, polarity, &mut cache);

        // Re-instantiate deferred overloads for the name being instantiated.
        // Only overloads carried under this name are scanned — this keeps
        // growth O(N) instead of O(3^N) when many SCC groups carry overloads.
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
        let Some(name_id) = name else {
            return result;
        };
        let Some(carried) = self.deferred.carried.get(&name_id) else {
            return result;
        };
        let num_carried = carried.len();
        let mut processed = vec![false; num_carried];
        loop {
            let mut made_progress = false;

            for (i, done) in processed.iter_mut().enumerate() {
                if *done {
                    continue;
                }

                // Extract fields by index to avoid holding a borrow on self.deferred
                // while calling &mut self methods below.
                let carried = &self.deferred.carried[&name_id];
                let ov_lhs = carried[i].constraint.lhs;
                let ov_rhs = carried[i].constraint.rhs;
                let ov_ret = carried[i].constraint.ret;
                let ov_op = carried[i].op;
                let ov_at = carried[i].constraint.at_expr;

                let any_extruded = cache.contains_key(&ov_lhs)
                    || cache.contains_key(&ov_rhs)
                    || cache.contains_key(&ov_ret);

                if any_extruded {
                    // For each operand, use the cached fresh var if available,
                    // otherwise extrude it now in positive polarity.
                    let get_or_extrude =
                        |id: TyId, this: &mut Self, cache: &mut FxHashMap<TyId, TyId>| -> TyId {
                            if let Some(&fresh) = cache.get(&id) {
                                fresh
                            } else {
                                this.extrude_inner(id, Polarity::Positive, cache)
                            }
                        };

                    let new_lhs = get_or_extrude(ov_lhs, self, &mut cache);
                    let new_rhs = get_or_extrude(ov_rhs, self, &mut cache);
                    let new_ret = get_or_extrude(ov_ret, self, &mut cache);

                    self.deferred
                        .active
                        .push(super::PendingConstraint::Overload(PendingOverload {
                            op: ov_op,
                            constraint: BinConstraint {
                                lhs: new_lhs,
                                rhs: new_rhs,
                                ret: new_ret,
                                at_expr: ov_at,
                            },
                        }));

                    *done = true;
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
        cache: &mut FxHashMap<TyId, TyId>,
    ) -> TyId {
        if let Some(&cached) = cache.get(&ty_id) {
            return cached;
        }

        // Bail out early if the deadline was exceeded. Return the original
        // type as-is — extrusion results will be incomplete but we avoid
        // spending unbounded time in the bounds-copying loop.
        if self.deadline_exceeded {
            return ty_id;
        }

        // Fast path: if the entire subtree is variable-free (only concrete
        // types / primitives, no type variables), it can never change during
        // extrusion regardless of level. Skip it in O(1).
        if self.types.variable_free.contains(&ty_id) {
            cache.insert(ty_id, ty_id);
            return ty_id;
        }

        // Fast path: non-polymorphic variables (at or below current level) and
        // primitive/TyVar concrete types are returned as-is without cloning.
        match self.types.storage.get(ty_id) {
            TypeEntry::Variable(v) if v.level < self.types.storage.current_level => {
                return ty_id;
            }
            TypeEntry::Concrete(Ty::Primitive(_) | Ty::TyVar(_)) => {
                // Leaf concrete types are trivially variable-free.
                self.types.variable_free.insert(ty_id);
                return ty_id;
            }
            _ => {}
        }

        // Guard against stack overflow on deeply nested type graphs.
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            // For polymorphic variables and structural concrete types, clone to
            // release the borrow on storage before calling &mut self methods.
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
                    // Clone only the bounds we need (not the entire TypeVariable).
                    let bounds_to_copy = match polarity {
                        Polarity::Positive => v.lower_bounds.clone(),
                        Polarity::Negative => v.upper_bounds.clone(),
                    };
                    let fresh = self.new_var();
                    cache.insert(ty_id, fresh);
                    self.link_extruded_var(ty_id, fresh, polarity, bounds_to_copy, cache);
                    // Named lower bounds flow to the fresh var through
                    // link_extruded_var — no manual provenance propagation.

                    fresh
                }
                TypeEntry::Variable(_) => {
                    // Non-polymorphic variables are handled by the fast path above.
                    unreachable!()
                }
                TypeEntry::Concrete(ty) => {
                    // Short-circuit optimisation: after recursing into children,
                    // if every child TyId is unchanged we reuse the original
                    // node instead of allocating a copy. Concrete types are
                    // immutable in TypeStorage so sharing is safe — only type
                    // *variables* need fresh copies for polymorphism.
                    //
                    // Macros for the two mechanical patterns that repeat across
                    // most Ty variant arms:
                    //
                    //   extrude_single!(child, polarity, rebuild) — List, Neg, Named
                    //   extrude_binary!(a, b, rebuild)            — Inter, Union

                    /// Extrude a single-child type. If the child is unchanged,
                    /// reuse the original node; otherwise rebuild with the new child.
                    macro_rules! extrude_single {
                        ($child:expr, $pol:expr, |$e:ident| $rebuild:expr) => {{
                            let $e = self.extrude_inner($child, $pol, cache);
                            if $e == $child {
                                return self.extrude_reuse(ty_id, cache);
                            }
                            self.alloc_concrete($rebuild)
                        }};
                    }

                    /// Extrude a two-child type (both covariant). If both children
                    /// are unchanged, reuse the original; otherwise rebuild.
                    macro_rules! extrude_binary {
                        ($a:expr, $b:expr, |$ea:ident, $eb:ident| $rebuild:expr) => {{
                            let $ea = self.extrude_inner($a, polarity, cache);
                            let $eb = self.extrude_inner($b, polarity, cache);
                            if $ea == $a && $eb == $b {
                                return self.extrude_reuse(ty_id, cache);
                            }
                            self.alloc_concrete($rebuild)
                        }};
                    }

                    let result = match ty {
                        Ty::Lambda { param, body } => {
                            // Insert a placeholder to handle recursive types.
                            let placeholder = self.new_var();
                            cache.insert(ty_id, placeholder);

                            let p = self.extrude_inner(param, polarity.flip(), cache);
                            let b = self.extrude_inner(body, polarity, cache);

                            if p == param && b == body {
                                // Nothing changed — reuse original. Overwrite
                                // the placeholder so later cache hits return
                                // the original, and remove the orphaned var.
                                return self.extrude_reuse(ty_id, cache);
                            }

                            let result = self.alloc_concrete(Ty::Lambda { param: p, body: b });

                            // Link placeholder to result.
                            self.constrain(result, placeholder).expect("extrude link");
                            self.constrain(placeholder, result).expect("extrude link");

                            result
                        }
                        Ty::List(elem) => {
                            extrude_single!(elem, polarity, |e| Ty::List(e))
                        }
                        Ty::AttrSet(attr) => {
                            let mut changed = false;
                            let new_fields: std::collections::BTreeMap<smol_str::SmolStr, TyId> =
                                attr.fields
                                    .iter()
                                    .map(|(k, &v)| {
                                        let e = self.extrude_inner(v, polarity, cache);
                                        if e != v {
                                            changed = true;
                                        }
                                        (k.clone(), e)
                                    })
                                    .collect();
                            let new_dyn = attr.dyn_ty.map(|d| {
                                let e = self.extrude_inner(d, polarity, cache);
                                if e != d {
                                    changed = true;
                                }
                                e
                            });
                            if !changed {
                                return self.extrude_reuse(ty_id, cache);
                            }
                            self.alloc_concrete(Ty::AttrSet(AttrSetTy {
                                fields: new_fields,
                                dyn_ty: new_dyn,
                                open: attr.open,
                                optional_fields: attr.optional_fields.clone(),
                            }))
                        }
                        // Primitives and TyVar are handled by the fast path above.
                        Ty::Primitive(_) | Ty::TyVar(_) => unreachable!(),
                        // Negation flips polarity, same as Lambda param.
                        Ty::Neg(inner) => {
                            extrude_single!(inner, polarity.flip(), |e| Ty::Neg(e))
                        }
                        // Intersection and Union: covariant — polarity preserved.
                        // This is what makes narrowing survive generalization:
                        // Inter(α, ¬T) extrudes to Inter(α', ¬T') where α' is
                        // the fresh call-site copy.
                        Ty::Inter(a, b) => {
                            extrude_binary!(a, b, |ea, eb| Ty::Inter(ea, eb))
                        }
                        Ty::Union(a, b) => {
                            extrude_binary!(a, b, |ea, eb| Ty::Union(ea, eb))
                        }
                        Ty::Named(name, inner) => {
                            extrude_single!(inner, polarity, |e| Ty::Named(name, e))
                        }
                    };

                    // Cache changed concrete types so repeated visits to the
                    // same TyId (from structural sharing) don't re-traverse
                    // the whole subtree. Safe because extrude_inner is
                    // deterministic for a given (ty_id, polarity, cache) triple.
                    cache.insert(ty_id, result);
                    result
                }
            }
        })
    }

    /// Mark a concrete type as unchanged during extrusion: cache it as
    /// identity-mapped and mark variable-free. Returns the original TyId
    /// for use in early-return.
    #[inline(always)]
    fn extrude_reuse(&mut self, ty_id: TyId, cache: &mut FxHashMap<TyId, TyId>) -> TyId {
        cache.insert(ty_id, ty_id);
        self.types.try_mark_variable_free(ty_id);
        ty_id
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
        bounds_to_copy: smallvec::SmallVec<[TyId; 4]>,
        cache: &mut FxHashMap<TyId, TyId>,
    ) {
        // In positive position, `original <: fresh`: the original flows into
        // the fresh var. We install the link as an upper bound on original and
        // copy the original's lower bounds (extruded) into fresh.
        //
        // In negative position, `fresh <: original`: symmetrically reversed.
        match polarity {
            Polarity::Positive => self.types.storage.add_upper_bound(original, fresh),
            Polarity::Negative => self.types.storage.add_lower_bound(original, fresh),
        }

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

    /// Maximum number of fixed-point iterations for pending constraint
    /// resolution. Prevents infinite loops from constraints that alternate
    /// between `PartialProgress` and `NoProgress`.
    const MAX_RESOLVE_ITERATIONS: usize = 256;

    fn resolve_pending(&mut self) -> Result<(), LocatedError> {
        // Fixed-point loop: keep trying until no more progress.
        let mut iterations = 0;
        loop {
            if self.past_deadline() {
                break;
            }

            iterations += 1;
            if iterations > Self::MAX_RESOLVE_ITERATIONS {
                log::warn!(
                    "resolve_pending hit iteration limit ({}) with {} constraints remaining",
                    Self::MAX_RESOLVE_ITERATIONS,
                    self.deferred.active.len(),
                );
                break;
            }

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
                    super::PendingConstraint::WithFallback(wf) => {
                        self.current_expr = wf.at_expr;
                        match self
                            .try_resolve_with_fallback(&wf)
                            .map_err(|err| self.locate_err(err))?
                        {
                            true => made_progress = true,
                            false => remaining.push(super::PendingConstraint::WithFallback(wf)),
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

    /// Try to resolve a deferred multi-`with` fallback constraint.
    ///
    /// Nix tries `with` environments inner-to-outer at runtime. We walk the
    /// env list (inner first) and pick the first env that definitely has the
    /// field. That env's value_ty is connected to the result variable. If an
    /// env is not yet concrete, we must wait (can't determine field presence).
    /// If all envs are concrete/closed and none has the field, it's an error.
    fn try_resolve_with_fallback(
        &mut self,
        wf: &PendingWithFallback,
    ) -> Result<bool, InferenceError> {
        let mut all_concrete_or_closed = true;

        for &(env_ty, value_ty) in &wf.envs {
            let Some(concrete) = self.types.find_concrete_through_inter(env_ty) else {
                // Not yet concrete — can't determine field presence. We must
                // stop here and wait, because an inner env that's still unknown
                // might have the field, and we must respect shadowing order.
                all_concrete_or_closed = false;
                break;
            };

            match concrete {
                Ty::AttrSet(ref attr) => {
                    if attr.fields.contains_key(&wf.field) {
                        // This env has the field — it's the winner. Connect
                        // its value variable to the result and stop.
                        self.constrain(value_ty, wf.result)?;
                        self.constrain(wf.result, value_ty)?;
                        return Ok(true);
                    } else if attr.dyn_ty.is_some() {
                        // Dynamic field type — field might be present.
                        all_concrete_or_closed = false;
                        break;
                    } else if attr.open {
                        // Open attrset — field might appear via future constraints.
                        all_concrete_or_closed = false;
                        break;
                    }
                    // Closed without the field: this env definitely doesn't
                    // have it, continue checking the next outer env.
                }
                _ => {
                    // Non-attrset: TypeMismatch is already caught by the
                    // constrain() in infer_reference. Treat as "no field here"
                    // and continue to the next env.
                }
            }
        }

        if all_concrete_or_closed {
            // Every env is known-concrete and none has the field.
            // Collect available fields from all envs for the error message.
            let mut available: Vec<smol_str::SmolStr> = Vec::new();
            for &(env_ty, _) in &wf.envs {
                if let Some(Ty::AttrSet(attr)) = self.types.find_concrete_through_inter(env_ty) {
                    for key in attr.fields.keys() {
                        if !available.contains(key) {
                            available.push(key.clone());
                        }
                    }
                }
            }
            return Err(InferenceError::MissingField {
                field: wf.field.clone(),
                available,
            });
        }

        // Still pending: at least one env is not concrete/closed, and no inner
        // env with the field has been found yet.
        Ok(false)
    }

    fn try_resolve_merge(&mut self, mg: &PendingMerge) -> Result<bool, InferenceError> {
        let lhs_concrete = self.types.find_concrete_through_inter(mg.lhs);
        let rhs_concrete = self.types.find_concrete_through_inter(mg.rhs);

        match (lhs_concrete, rhs_concrete) {
            (Some(Ty::AttrSet(lhs_attr)), Some(Ty::AttrSet(rhs_attr))) => {
                let merged = lhs_attr.merge(rhs_attr);
                let merged_id = self.alloc_concrete(Ty::AttrSet(merged));
                self.constrain(merged_id, mg.ret)?;
                self.constrain(mg.ret, merged_id)?;
                Ok(true)
            }
            (Some(lhs), Some(rhs)) => Err(InferenceError::InvalidAttrMerge(Box::new((
                lhs.clone(),
                rhs.clone(),
            )))),
            _ => Ok(false),
        }
    }

    /// Compact the bounds graph for an SCC group's type slots.
    ///
    /// Runs three passes over `[slots_before..len)`:
    /// 1. **Pin**: Replace fully-determined variables with their concrete type.
    /// 2. **Dedup**: Remove duplicate bounds on remaining variables.
    /// 3. **Variable-free propagation**: Newly-concrete entries may make parents
    ///    variable-free, enabling O(1) extrusion short-circuits.
    fn compact_scc_graph(&mut self, slots_before: usize) {
        let t_compact = Instant::now();
        let vf_before = self.types.variable_free.len();

        // Pass 1 + 2: pin and dedup in a single scan.
        let (pinned, deduped) = self.types.compact_pinned_variables(slots_before);

        // Pass 3: propagate variable-free status for all entries in the range.
        // Newly-compacted entries are now concrete and may enable their parents
        // to become variable-free too.
        let len = self.types.storage.len();
        for idx in slots_before..len {
            self.types.try_mark_variable_free(TyId(idx as u32));
        }

        // Pass 4: prune carried overloads whose operands are both concrete.
        // These are fully resolved and would never contribute new constraints
        // during future extrusions — keeping them would cause stale entries
        // to accumulate.
        let carried_before: usize = self.deferred.carried.values().map(|v| v.len()).sum();
        let types = &self.types;
        for overloads in self.deferred.carried.values_mut() {
            overloads.retain(|ov| {
                let lhs_concrete = types
                    .find_concrete_through_inter(ov.constraint.lhs)
                    .is_some();
                let rhs_concrete = types
                    .find_concrete_through_inter(ov.constraint.rhs)
                    .is_some();
                !(lhs_concrete && rhs_concrete)
            });
        }
        self.deferred.carried.retain(|_, v| !v.is_empty());
        let carried_after: usize = self.deferred.carried.values().map(|v| v.len()).sum();
        let pruned = carried_before - carried_after;

        let vf_after = self.types.variable_free.len();
        let elapsed = t_compact.elapsed();
        if pinned > 0 || pruned > 0 || elapsed.as_millis() > 5 {
            log::info!(
                "  compact_scc_graph: {:.1}ms, pinned {}, deduped {}, variable_free {} → {}, carried pruned {}",
                elapsed.as_secs_f64() * 1000.0,
                pinned,
                deduped,
                vf_before,
                vf_after,
                pruned,
            );
        }
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
        // Collect child ExprIds (all Copy) to avoid cloning the full Expr.
        let mut children = Vec::new();
        self.module[expr].walk_child_exprs(|child| children.push(child));
        for child in children {
            self.lift_expr_slots(child);
        }
    }

    /// Walk the type graph reachable from `ty_id` and lift any variables
    /// below the current level to the current level. This ensures that
    /// variables from stub types (interned at level 0 during annotation
    /// processing) are treated as polymorphic during extrusion at consumer
    /// call sites.
    fn lift_reachable_vars(&mut self, ty_id: TyId) {
        let mut visited = FxHashSet::default();
        self.lift_reachable_vars_inner(ty_id, &mut visited);
    }

    fn lift_reachable_vars_inner(&mut self, ty_id: TyId, visited: &mut FxHashSet<TyId>) {
        if !visited.insert(ty_id) {
            return;
        }

        // Variable-free subtrees contain no type variables to lift.
        if self.types.variable_free.contains(&ty_id) {
            return;
        }

        if let Some(v) = self.types.storage.get_var(ty_id) {
            let needs_lift = v.level < self.types.storage.current_level;
            // Clone just the bounds (SmallVec<[TyId; 4]>, cheap) to release borrow.
            let lower = v.lower_bounds.clone();
            let upper = v.upper_bounds.clone();

            if needs_lift {
                self.types
                    .storage
                    .set_var_level(ty_id, self.types.storage.current_level);
            }
            // Recurse into bounds to lift any stub variables reachable
            // through the bounds graph.
            for bound in lower {
                self.lift_reachable_vars_inner(bound, visited);
            }
            for bound in upper {
                self.lift_reachable_vars_inner(bound, visited);
            }
            return;
        }

        // Concrete type — clone and recurse into children.
        let entry = self.types.storage.get(ty_id).clone();
        if let TypeEntry::Concrete(ty) = entry {
            match ty {
                Ty::Lambda { param, body } => {
                    self.lift_reachable_vars_inner(param, visited);
                    self.lift_reachable_vars_inner(body, visited);
                }
                Ty::List(elem) => {
                    self.lift_reachable_vars_inner(elem, visited);
                }
                Ty::AttrSet(ref attr) => {
                    for &field_ty in attr.fields.values() {
                        self.lift_reachable_vars_inner(field_ty, visited);
                    }
                    if let Some(dyn_ty) = attr.dyn_ty {
                        self.lift_reachable_vars_inner(dyn_ty, visited);
                    }
                }
                Ty::Union(a, b) | Ty::Inter(a, b) => {
                    self.lift_reachable_vars_inner(a, visited);
                    self.lift_reachable_vars_inner(b, visited);
                }
                Ty::Neg(inner) => {
                    self.lift_reachable_vars_inner(inner, visited);
                }
                Ty::Named(_, inner) => {
                    self.lift_reachable_vars_inner(inner, visited);
                }
                Ty::Primitive(_) | Ty::TyVar(_) => {}
            }
        }
    }

    /// If `name_slot` (a variable) has a Named lower bound from a type
    /// annotation, wrap `poly_ty` in the same Named. This ensures extrusion
    /// preserves the alias name at usage sites.
    fn wrap_named_if_annotated(&mut self, name_slot: TyId, poly_ty: TyId) -> TyId {
        if let Some(v) = self.types.storage.get_var(name_slot) {
            for &lb in &v.lower_bounds.clone() {
                if let TypeEntry::Concrete(Ty::Named(name, _)) = self.types.storage.get(lb) {
                    let name = name.clone();
                    return self.alloc_concrete(Ty::Named(name, poly_ty));
                }
            }
        }
        poly_ty
    }
}
