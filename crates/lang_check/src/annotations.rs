// ==============================================================================
// Annotation interning — ParsedTy -> TyId subsystem
// ==============================================================================
//
// Converts parsed type annotations (doc comments, .tix stubs) and imported
// OutputTy values into inference-side TyIds: alias expansion, recursive-alias
// knot tying, frozen import wrapping, and annotation-bound propagation.
// Split out of lib.rs; all methods are on CheckCtx.

use std::path::PathBuf;
use std::sync::Arc;

use comment_parser::{parse_and_collect, parse_context_annotation, ParsedTy, TypeVarValue};

use lang_ast::{Expr, ExprId, NameId};
use lang_ty::{OutputTy, OwnedTy, TyRef, TypeArena};
use rustc_hash::FxHashMap as HashMap;
use smol_str::SmolStr;

use crate::{
    parsed_ty_arity, uppercase_primitive_alias, CheckCtx, LocatedError, Polarity, Ty, TyId, Warning,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum AliasKey {
    Local(SmolStr),
    Imported(PathBuf, SmolStr),
}

pub(crate) struct InProgressAlias {
    /// Variable handed to back-references; allocated on first re-entry only,
    /// so non-recursive aliases pay nothing.
    placeholder: Option<TyId>,
    guard_depth_at_entry: usize,
}

/// State threaded through one annotation's interning to detect and tie
/// recursive alias references.
#[derive(Default)]
pub(crate) struct AliasInternState {
    in_progress: HashMap<AliasKey, InProgressAlias>,
    /// Number of List/Lambda/AttrSet constructors above the current position.
    guard_depth: usize,
}

impl CheckCtx<'_> {
    // ==========================================================================
    // Type annotation interning (doc comment → internal types)
    // ==========================================================================

    // ==========================================================================
    // OutputTy interning (import results → internal types)
    // ==========================================================================

    /// Intern an OwnedTy as a single frozen TyId. Instead of eagerly
    /// converting the entire type tree into TyIds (O(N) allocations),
    /// wraps it in `Ty::Frozen(OwnedTy)` — one allocation. Fields are
    /// materialized on demand when `constrain` encounters the Frozen type.
    pub(crate) fn intern_frozen_owned_ty(&mut self, owned: &OwnedTy) -> TyId {
        self.alloc_concrete(Ty::Frozen(owned.clone()))
    }

    /// Intern an OwnedTy into this file's TypeStorage, creating fresh TyIds.
    ///
    /// Each TyVar(n) in the OwnedTy maps to a fresh variable (via a local
    /// HashMap). This ensures imported types are fully isolated from the
    /// source file's TypeStorage — constraints applied in this file cannot
    /// propagate back to the imported file.
    pub(crate) fn intern_output_ty(&mut self, owned: &OwnedTy) -> TyId {
        let mut var_map: HashMap<u32, TyId> = HashMap::default();
        let mut ref_cache: HashMap<TyRef, TyId> = HashMap::default();
        self.intern_output_ty_inner(&owned.arena, owned.root, &mut var_map, &mut ref_cache)
    }

    pub(crate) fn intern_output_ty_inner(
        &mut self,
        arena: &TypeArena,
        ty: TyRef,
        var_map: &mut HashMap<u32, TyId>,
        ref_cache: &mut HashMap<TyRef, TyId>,
    ) -> TyId {
        // Preserve DAG sharing: if we already interned this TyRef, reuse it.
        // Without this, shared subtrees in the TypeArena expand exponentially
        // (e.g. common.nix's output type caused a 1.5GB allocation on chromium).
        // Checked before the stack guard so cache hits skip it.
        if let Some(&cached) = ref_cache.get(&ty) {
            return cached;
        }
        lang_ast::stack::with_stack(|| self.intern_output_ty_guarded(arena, ty, var_map, ref_cache))
    }

    pub(crate) fn intern_output_ty_guarded(
        &mut self,
        arena: &TypeArena,
        ty: TyRef,
        var_map: &mut HashMap<u32, TyId>,
        ref_cache: &mut HashMap<TyRef, TyId>,
    ) -> TyId {
        let result = match &arena[ty] {
            OutputTy::TyVar(n) => *var_map.entry(*n).or_insert_with(|| self.new_var()),
            OutputTy::Primitive(prim) => self.alloc_prim(*prim),
            OutputTy::List(inner) => {
                let inner = *inner;
                let elem = self.intern_output_ty_inner(arena, inner, var_map, ref_cache);
                self.alloc_concrete(Ty::List(elem))
            }
            OutputTy::Lambda { param, body } => {
                let (param, body) = (*param, *body);
                let p = self.intern_output_ty_inner(arena, param, var_map, ref_cache);
                let b = self.intern_output_ty_inner(arena, body, var_map, ref_cache);
                self.alloc_concrete(Ty::Lambda { param: p, body: b })
            }
            OutputTy::AttrSet(attr) => {
                let fields_vec: Vec<_> = attr.fields.iter().map(|(k, &v)| (k.clone(), v)).collect();
                let dyn_ty = attr.dyn_ty;
                let open = attr.open;
                let optional_fields = attr.optional_fields.clone();

                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in fields_vec {
                    let field_ty = self.intern_output_ty_inner(arena, v, var_map, ref_cache);
                    fields.insert(k, field_ty);
                }
                let dyn_ty =
                    dyn_ty.map(|d| self.intern_output_ty_inner(arena, d, var_map, ref_cache));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open,
                    optional_fields,
                }))
            }
            // Union: create a fresh variable with each member as a lower bound.
            OutputTy::Union(members) => {
                let members = members.clone();
                let var = self.new_var();
                for m in &members {
                    let member_ty = self.intern_output_ty_inner(arena, *m, var_map, ref_cache);
                    self.types.storage.add_lower_bound(var, member_ty);
                }
                var
            }
            // Intersection: create a fresh variable with each member as an upper bound.
            OutputTy::Intersection(members) => {
                let members = members.clone();
                let var = self.new_var();
                for m in &members {
                    let member_ty = self.intern_output_ty_inner(arena, *m, var_map, ref_cache);
                    self.types.storage.add_upper_bound(var, member_ty);
                }
                var
            }
            // Named: if the alias registry has a definition for this name,
            // re-instantiate from the alias definition (with fresh generic
            // variables) instead of interning the potentially-monomorphized
            // inner type from the exporting file. This prevents monomorphized
            // generics in dep files from polluting the importing file's types.
            OutputTy::Named(name, inner) => {
                let (name, inner) = (name.clone(), *inner);
                if let Some(alias_body) = self.type_aliases.get(&name).cloned() {
                    let fresh_inner = self.intern_fresh_ty(alias_body);
                    self.alloc_concrete(Ty::Named(name, fresh_inner))
                } else {
                    let inner_id = self.intern_output_ty_inner(arena, inner, var_map, ref_cache);
                    self.alloc_concrete(Ty::Named(name, inner_id))
                }
            }
            // Negation: intern the inner type and wrap in Ty::Neg.
            OutputTy::Neg(inner) => {
                let inner = *inner;
                let inner_id = self.intern_output_ty_inner(arena, inner, var_map, ref_cache);
                self.alloc_concrete(Ty::Neg(inner_id))
            }
            // Bottom/Top: fresh unconstrained variables.
            OutputTy::Bottom => self.new_var(),
            OutputTy::Top => self.new_var(),
            // Extern: wrap back as a Frozen type for inference.
            OutputTy::Extern(owned) => self.intern_frozen_owned_ty(owned),
        };

        ref_cache.insert(ty, result);
        result
    }

    /// If `name_id` has a doc comment type annotation (e.g. `/** type: x :: int */`),
    /// constrain `ty` to match the declared type. Returns Ok(()) if no annotation
    /// is present or if the constraint succeeds.
    pub(crate) fn apply_type_annotation(
        &mut self,
        name_id: NameId,
        ty: TyId,
    ) -> Result<(), LocatedError> {
        // Extract doc strings without borrowing self mutably so we can
        // emit diagnostics for parse errors afterwards.
        let docs = self.module.type_dec_map.docs_for_name(name_id).cloned();
        let name_str = self.module[name_id].text.clone();

        let type_annotation = docs.and_then(|docs| {
            let mut all_decls = Vec::new();
            for doc in docs.iter() {
                match parse_and_collect(doc) {
                    Ok(decls) => all_decls.extend(decls),
                    Err(err) => {
                        self.emit_warning(Warning::AnnotationParseError {
                            name: name_str.clone(),
                            error: err.to_string().into(),
                        });
                    }
                }
            }
            all_decls.into_iter().find_map(|decl| {
                if decl.identifier == *name_str {
                    Some(decl.type_expr)
                } else {
                    None
                }
            })
        });

        if let Some(known_ty) = type_annotation {
            // Intersection-of-lambda annotations declare overloaded function types.
            // Verifying each component against the body separately requires
            // re-inference (not yet supported). Accept the annotation as the
            // declared type for callers without constraining the body.
            // This check runs before the arity guard because an intersection's
            // top-level arity is 0 (it's not a Lambda node), which would
            // incorrectly trigger the arity mismatch.
            if known_ty.is_intersection_of_lambdas() {
                let annotation_ty = self.intern_fresh_ty(known_ty);
                // Add annotation as lower bound of the name slot for display
                // (no constraint propagation — avoids the false errors that
                // caused the skip). Use the name slot (always a variable),
                // not `ty` which may be concrete from infer_expr.
                let name_slot = self.ty_for_name_direct(name_id);
                self.types.storage.add_lower_bound(name_slot, annotation_ty);
                self.propagate_annotation_bounds(annotation_ty, name_id);
                self.emit_warning(Warning::AnnotationUnchecked {
                    name: self.module[name_id].text.clone(),
                    reason: "intersection-of-function annotations are accepted as declared types \
                             but not verified against the body"
                        .into(),
                });
                return Ok(());
            }

            // Guard: skip annotations whose arity is LESS than the expression's
            // visible lambda depth. This means the doc comment claims fewer
            // arguments than the function actually has (e.g. `foo :: a -> a` on
            // a two-argument function `x: y: ...`). Applying such an annotation
            // would partially constrain the type table before failing, corrupting
            // downstream inference. Emit a warning instead.
            //
            // An annotation with MORE arrows than visible lambdas is fine — the
            // function body may return a function (eta-reduction), e.g.
            // `escape :: [string] -> string -> string` on `escape = list: ...`
            // where the body returns `string -> string`.
            let annot_arity = parsed_ty_arity(&known_ty);
            let expr_arity = self
                .binding_exprs
                .get(&name_id)
                .map(|&e| self.expr_lambda_arity(e))
                .unwrap_or(0);
            if annot_arity < expr_arity && expr_arity > 0 {
                self.emit_warning(Warning::AnnotationArityMismatch {
                    name: self.module[name_id].text.clone(),
                    annotation_arity: annot_arity,
                    expression_arity: expr_arity,
                });
                return Ok(());
            }

            // Annotations that contain union types in function parameters can't
            // be verified without full narrowing support (e.g. `isAttrs`/`isList`
            // branching). Applying bidirectional constraints on such annotations
            // pushes all union members as lower bounds into the inferred param,
            // causing false type errors. Skip these with a warning.
            //
            // Only skip for actual function bindings (expr_arity > 0). For
            // non-function bindings (lambda params, simple let-bindings), there's
            // no body-vs-annotation conflict — the constraint is safe. This
            // prevents over-skipping where a nested union in a field type (e.g.
            // `module pkgs { val mkDerivation :: (A | B) -> D; }`) would
            // incorrectly cause the entire annotation to be dropped.
            //
            // Expand alias references to detect unions hidden behind type aliases
            // (e.g. `Nullable = int | null`).
            let has_union = known_ty.contains_union_resolving(&|name| self.type_aliases.get(name));
            if has_union && expr_arity > 0 {
                // Still intern for display purposes, but don't apply constraints.
                // Add annotation as lower bound of the name slot so
                // canonicalization shows the alias.
                let annotation_ty = self.intern_fresh_ty(known_ty);
                let name_slot = self.ty_for_name_direct(name_id);
                self.types.storage.add_lower_bound(name_slot, annotation_ty);
                self.propagate_annotation_bounds(annotation_ty, name_id);
                return Ok(());
            }

            let annotation_ty = self.intern_fresh_ty(known_ty);
            self.constrain_equal(ty, annotation_ty)?;
            // constrain_equal unwraps Named transparently, so the Named
            // wrapper doesn't flow into bounds. Add it explicitly as a
            // lower bound on the name slot for display.
            let name_slot = self.ty_for_name_direct(name_id);
            self.types.storage.add_lower_bound(name_slot, annotation_ty);
            self.propagate_annotation_bounds(annotation_ty, name_id);
        }

        Ok(())
    }

    /// Walk an interned annotation type and the corresponding expression in
    /// parallel, adding the annotation's param types as lower bounds on the
    /// inferred param types at each Lambda level.
    ///
    /// For `renderArg :: BwrapArg -> string`, the annotation creates a
    /// `Lambda { param: Named("BwrapArg", ...), body: ... }`. The expression
    /// is `Lambda { param: Some(name_id), body }`. We add the annotation's
    /// param (which may be `Named`) as a lower bound of the inferred param
    /// so that canonicalization shows "BwrapArg" instead of the expanded type.
    pub(crate) fn propagate_annotation_bounds(&mut self, annotation_ty: TyId, name_id: NameId) {
        let Some(&expr_id) = self.binding_exprs.get(&name_id) else {
            return;
        };
        self.propagate_annotation_bounds_inner(annotation_ty, expr_id);
    }

    pub(crate) fn propagate_annotation_bounds_inner(
        &mut self,
        annotation_ty: TyId,
        expr_id: ExprId,
    ) {
        // Get the annotation type structure. Unwrap Named wrappers.
        let annot_entry = self.types.storage.get(annotation_ty).clone();
        let (annot_param, annot_body) = match annot_entry {
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                return self.propagate_annotation_bounds_inner(inner, expr_id);
            }
            crate::storage::TypeEntry::Concrete(Ty::Lambda { param, body }) => (param, body),
            _ => return,
        };

        // Get the expression structure.
        let expr = self.module[expr_id].clone();
        let (param_name, body_expr) = match expr {
            Expr::Lambda { param, body, .. } => (param, body),
            _ => return,
        };

        // Add annotation param (which may be Named) as both lower and upper
        // bound of the inferred param, so canonicalization picks up the alias
        // name regardless of polarity. Both are needed because link_extruded_var
        // copies lower bounds for positive polarity and upper bounds for negative
        // polarity (Lambda params are extruded in negative polarity).
        if let Some(param_name_id) = param_name {
            let inferred_param_ty = self.ty_for_name_direct(param_name_id);
            self.types
                .storage
                .add_lower_bound(inferred_param_ty, annot_param);
            self.types
                .storage
                .add_upper_bound(inferred_param_ty, annot_param);
        }

        // Recurse into the body to transfer deeper param annotations.
        self.propagate_annotation_bounds_inner(annot_body, body_expr);
    }

    /// Resolve type-level operators (Param, Return, FieldAccess) by expanding
    /// aliases and destructuring at the ParsedTy level. Depth-guarded to 20.
    pub(crate) fn resolve_type_operators(&self, ty: &ParsedTy) -> ParsedTy {
        self.resolve_type_operators_inner(ty, 0)
    }

    pub(crate) fn resolve_type_operators_inner(&self, ty: &ParsedTy, depth: usize) -> ParsedTy {
        if depth > 20 {
            return ty.clone();
        }
        match ty {
            ParsedTy::Param(inner) => {
                let resolved = self.resolve_type_operators_inner(&inner.0, depth + 1);
                let expanded = self.expand_parsed_aliases(&resolved, depth + 1);
                match expanded {
                    ParsedTy::Lambda { param, .. } => (*param.0).clone(),
                    _ => ty.clone(), // can't extract — keep as-is, will degrade to fresh var
                }
            }
            ParsedTy::Return(inner) => {
                let resolved = self.resolve_type_operators_inner(&inner.0, depth + 1);
                let expanded = self.expand_parsed_aliases(&resolved, depth + 1);
                match expanded {
                    ParsedTy::Lambda { body, .. } => (*body.0).clone(),
                    _ => ty.clone(),
                }
            }
            ParsedTy::FieldAccess(inner, key) => {
                let resolved = self.resolve_type_operators_inner(&inner.0, depth + 1);
                let expanded = self.expand_parsed_aliases(&resolved, depth + 1);
                match expanded {
                    ParsedTy::AttrSet(ref attr) => {
                        if let Some(field_ty) = attr.fields.get(key.as_str()) {
                            (*field_ty.0).clone()
                        } else {
                            ty.clone() // field not found — keep, will degrade
                        }
                    }
                    _ => ty.clone(),
                }
            }
            // For all other variants, return as-is.
            _ => ty.clone(),
        }
    }

    /// Expand type alias references in a ParsedTy. Replaces Reference("Foo")
    /// with the alias body from the registry. Depth-guarded to prevent cycles.
    pub(crate) fn expand_parsed_aliases(&self, ty: &ParsedTy, depth: usize) -> ParsedTy {
        if depth > 20 {
            return ty.clone();
        }
        match ty {
            ParsedTy::TyVar(TypeVarValue::Reference(name)) => {
                if let Some(alias_body) = self.type_aliases.get(name.as_str()).cloned() {
                    self.expand_parsed_aliases(&alias_body, depth + 1)
                } else {
                    ty.clone()
                }
            }
            _ => ty.clone(),
        }
    }

    /// Intern a ParsedTy with fresh type variables for each free generic var
    /// and alias resolution for Reference vars. Each call produces an independent
    /// "instance" — analogous to polymorphic instantiation.
    pub(crate) fn intern_fresh_ty(&mut self, ty: ParsedTy) -> TyId {
        let mut st = AliasInternState::default();
        self.intern_fresh_ty_inner(ty, &mut st)
    }

    pub(crate) fn intern_fresh_ty_inner(
        &mut self,
        ty: ParsedTy,
        st: &mut AliasInternState,
    ) -> TyId {
        // Pre-resolve type operators (Param, Return, FieldAccess) at the
        // ParsedTy level before interning. This expands aliases and
        // destructures types so the result is a plain ParsedTy.
        let ty = self.resolve_type_operators(&ty);

        // Generic vars get one fresh variable per instance. Alias references
        // are resolved lazily during the walk (see `intern_alias_ref`) so that
        // recursive aliases can tie the knot instead of unfolding forever.
        let subs: HashMap<TypeVarValue, TyId> = ty
            .free_vars()
            .into_iter()
            .filter(|var| matches!(var, TypeVarValue::Generic(_)))
            .map(|var| (var, self.new_var()))
            .collect();

        let mut memo = HashMap::default();
        self.intern_parsed_ty(&ty, &subs, st, &mut memo)
    }

    /// Resolve one alias occurrence. `memo` is per alias body so repeated
    /// references within one body share an instance; `st.in_progress` spans
    /// the whole annotation so a back-reference to an alias being interned
    /// returns a placeholder variable instead of recursing.
    pub(crate) fn intern_alias_ref(
        &mut self,
        key: AliasKey,
        body: ParsedTy,
        st: &mut AliasInternState,
        memo: &mut HashMap<AliasKey, TyId>,
    ) -> TyId {
        if let Some(&id) = memo.get(&key) {
            return id;
        }

        if let Some(entry) = st.in_progress.get_mut(&key) {
            // Unguarded cycle (`type A = A`, `type A = A | int`): no constructor
            // between the alias and its own reference, so there is no finite
            // type to tie a knot on. Degrade to a fresh variable.
            if st.guard_depth == entry.guard_depth_at_entry {
                return self.types.new_var();
            }
            if let Some(p) = entry.placeholder {
                return p;
            }
            let p = self.types.new_var();
            entry.placeholder = Some(p);
            return p;
        }

        st.in_progress.insert(
            key.clone(),
            InProgressAlias {
                placeholder: None,
                guard_depth_at_entry: st.guard_depth,
            },
        );
        let inner = self.intern_fresh_ty_inner(body, st);
        let entry = st
            .in_progress
            .remove(&key)
            .expect("in_progress entry inserted above");

        let result = match &key {
            AliasKey::Local(name) => self.alloc_concrete(Ty::Named(name.clone(), inner)),
            AliasKey::Imported(..) => inner,
        };

        // Tie the knot: the placeholder handed to back-references is pinned
        // to the finished type. Direct bounds suffice — the placeholder is
        // fresh, so there is nothing to propagate.
        if let Some(p) = entry.placeholder {
            self.types.storage.add_lower_bound(p, result);
            self.types.storage.add_upper_bound(p, result);
        }

        memo.insert(key, result);
        result
    }

    pub(crate) fn intern_parsed_ty(
        &mut self,
        ty: &ParsedTy,
        substitutions: &HashMap<TypeVarValue, TyId>,
        st: &mut AliasInternState,
        memo: &mut HashMap<AliasKey, TyId>,
    ) -> TyId {
        match ty {
            ParsedTy::TyVar(TypeVarValue::Reference(name)) => {
                // `Any` is treated as a wildcard — each occurrence gets its own
                // fresh variable so `Any -> Any` doesn't unify the two positions.
                // This matches the noogle convention where `Any` means "some type"
                // rather than "the same type everywhere".
                if name == "Any" && self.type_aliases.get("Any").is_none() {
                    return self.new_var();
                }
                if let Some(body) = self.type_aliases.get(name).cloned() {
                    let key = AliasKey::Local(SmolStr::from(name.as_str()));
                    return self.intern_alias_ref(key, body, st, memo);
                }
                // Nixpkgs doc comments conventionally use uppercase primitive
                // names (String, Bool, Int, etc.). Map them to the
                // corresponding lowercase primitive type.
                if let Some(prim) = uppercase_primitive_alias(name) {
                    return self.alloc_prim(prim);
                }
                // Unknown reference — degrade to fresh variable.
                self.new_var()
            }
            ParsedTy::TyVar(var) => {
                match substitutions.get(var) {
                    Some(replacement) => *replacement,
                    None => {
                        // free_vars() missed this variable — shouldn't happen,
                        // but degrade to a fresh variable instead of panicking.
                        debug_assert!(
                            false,
                            "No substitution for {var:?}; free_vars() may be incomplete"
                        );
                        self.new_var()
                    }
                }
            }
            ParsedTy::Primitive(prim) => self.alloc_prim(*prim),
            // List/Lambda/AttrSet are the constructors that guard alias
            // recursion: a back-reference beneath one of them denotes a
            // finite, well-formed recursive type.
            ParsedTy::List(inner) => {
                st.guard_depth += 1;
                let new_inner = self.intern_parsed_ty(&inner.0, substitutions, st, memo);
                st.guard_depth -= 1;
                self.alloc_concrete(Ty::List(new_inner))
            }
            ParsedTy::Lambda { param, body } => {
                st.guard_depth += 1;
                let new_param = self.intern_parsed_ty(&param.0, substitutions, st, memo);
                let new_body = self.intern_parsed_ty(&body.0, substitutions, st, memo);
                st.guard_depth -= 1;
                self.alloc_concrete(Ty::Lambda {
                    param: new_param,
                    body: new_body,
                })
            }
            ParsedTy::AttrSet(attr) => {
                st.guard_depth += 1;
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let new_v = self.intern_parsed_ty(&v.0, substitutions, st, memo);
                    fields.insert(k.clone(), new_v);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_parsed_ty(&d.0, substitutions, st, memo));
                st.guard_depth -= 1;
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                }))
            }
            // Union annotations: build a concrete Ty::Union tree instead of a
            // variable with lower bounds. This keeps types like `path | string`
            // fully concrete, which lets the extrusion short-circuit fire for
            // parent types (e.g. Derivation, Pkgs) that contain union fields.
            // Semantics are equivalent: constrain(Union(a,b), T) distributes to
            // constrain(a, T) ∧ constrain(b, T), same as the old variable approach.
            ParsedTy::Union(members) => {
                let tys: Vec<TyId> = members
                    .iter()
                    .map(|m| self.intern_parsed_ty(&m.0, substitutions, st, memo))
                    .collect();
                tys.into_iter()
                    .reduce(|acc, ty| self.alloc_concrete(Ty::Union(acc, ty)))
                    .unwrap_or_else(|| self.new_var())
            }
            // Intersection annotations: build a concrete Ty::Inter tree.
            // Same rationale as Union above — keeps the type fully concrete.
            ParsedTy::Intersection(members) => {
                let tys: Vec<TyId> = members
                    .iter()
                    .map(|m| self.intern_parsed_ty(&m.0, substitutions, st, memo))
                    .collect();
                tys.into_iter()
                    .reduce(|acc, ty| self.alloc_concrete(Ty::Inter(acc, ty)))
                    .unwrap_or_else(|| self.new_var())
            }
            // Top/Bottom: a fresh unconstrained variable is the correct
            // representation in the bounds system. For Top (any), no upper
            // bounds means "accepts anything" in negative position; for
            // Bottom (never), no lower bounds means "produces nothing" in
            // positive position. The variable won't reject constraints from
            // usage, so `any` effectively behaves like a generic parameter
            // rather than a true ⊤ — which is the desired behavior for
            // annotations like `val f :: any -> int`.
            ParsedTy::Top | ParsedTy::Bottom => self.new_var(),

            // typeof varname — resolve to the inferred type of a local binding.
            // The binding must be in an already-generalized SCC (in poly_type_env).
            ParsedTy::TypeOf(name) => {
                // Find the NameId for this binding name.
                let name_id = self
                    .module
                    .names()
                    .find(|(_, n)| n.text.as_str() == name.as_str())
                    .map(|(id, _)| id);
                match name_id {
                    Some(name_id) => {
                        if let Some(&poly_ty) = self.poly_type_env.get(name_id) {
                            // Extrude a fresh instance, same as a normal reference.
                            self.extrude(poly_ty, Polarity::Positive, Some(name_id))
                        } else {
                            // Not yet generalized (same or later SCC). Degrade to
                            // fresh var — the annotation will have no constraining
                            // effect, which is the safe fallback.
                            // TODO: emit a diagnostic for this case
                            self.new_var()
                        }
                    }
                    None => {
                        // Unknown name. Degrade to fresh var.
                        // TODO: emit a diagnostic for this case
                        self.new_var()
                    }
                }
            }

            // Param/Return/FieldAccess that survived resolve_type_operators
            // (e.g. Param(typeof f) where typeof needs TyId-level resolution).
            // Intern the inner type, then inspect the concrete result.
            ParsedTy::Param(inner) => {
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions, st, memo);
                self.extract_param_ty(inner_ty)
            }
            ParsedTy::Return(inner) => {
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions, st, memo);
                self.extract_return_ty(inner_ty)
            }
            ParsedTy::FieldAccess(inner, key) => {
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions, st, memo);
                self.extract_field_ty(inner_ty, key)
            }

            // import("./path.nix").TypeName — resolve from imported type exports.
            ParsedTy::ImportType(path, name) => {
                if let Some(base) = &self.file_base_dir {
                    let resolved = base.join(path);
                    if let Some(exports) = self.imported_type_exports.get(&resolved) {
                        if let Some(alias_body) = exports.get(name.as_str()).cloned() {
                            let key = AliasKey::Imported(resolved, name.clone());
                            return self.intern_alias_ref(key, alias_body, st, memo);
                        }
                    }
                }
                // Unresolved — degrade to fresh var.
                // TODO: emit diagnostic
                self.new_var()
            }

            // typeof import("./path.nix") — resolve to the inferred root type
            // of another file.
            ParsedTy::TypeOfImport(path) => {
                if let Some(base) = &self.file_base_dir {
                    let resolved = base.join(path);
                    if let Some(owned_ty) = self.typeof_import_types.get(&resolved).cloned() {
                        return self.intern_frozen_owned_ty(&owned_ty);
                    }
                }
                // Unresolved — degrade to fresh var.
                // TODO: emit diagnostic
                self.new_var()
            }
        }
    }

    /// Extract the parameter type from a TyId that should be a Lambda.
    /// Follows Named wrappers and single-lower-bound variables.
    pub(crate) fn extract_param_ty(&mut self, ty: TyId) -> TyId {
        match self.types.storage.get(ty).clone() {
            crate::storage::TypeEntry::Concrete(Ty::Lambda { param, .. }) => param,
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                self.extract_param_ty(inner)
            }
            _ => self.new_var(), // Not a function — degrade
        }
    }

    /// Extract the return type from a TyId that should be a Lambda.
    pub(crate) fn extract_return_ty(&mut self, ty: TyId) -> TyId {
        match self.types.storage.get(ty).clone() {
            crate::storage::TypeEntry::Concrete(Ty::Lambda { body, .. }) => body,
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                self.extract_return_ty(inner)
            }
            _ => self.new_var(),
        }
    }

    /// Extract a field's type from a TyId that should be an AttrSet.
    pub(crate) fn extract_field_ty(&mut self, ty: TyId, key: &str) -> TyId {
        match self.types.storage.get(ty).clone() {
            crate::storage::TypeEntry::Concrete(Ty::AttrSet(ref attr)) => {
                if let Some(&field_ty) = attr.fields.get(key) {
                    field_ty
                } else {
                    self.new_var() // Field not found — degrade
                }
            }
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                self.extract_field_ty(inner, key)
            }
            _ => self.new_var(),
        }
    }

    /// Check whether a lambda expression has a `/** context: <name> */` doc
    /// comment annotation. If so, load the named context's stubs and return
    /// the arg→type map.
    ///
    /// Results are NOT cached because context annotations are rare (typically
    /// one per file at most), and the cost of re-parsing is negligible compared
    /// to inference.
    pub(crate) fn resolve_doc_comment_context(
        &mut self,
        expr_id: ExprId,
    ) -> Option<Arc<HashMap<smol_str::SmolStr, ParsedTy>>> {
        let docs = self.module.type_dec_map.docs_for_expr(expr_id)?;
        for doc in docs {
            if let Some(context_name) = parse_context_annotation(doc) {
                // Arc::make_mut triggers a clone only when the refcount > 1
                // AND this rare code path fires (context doc comments).
                match Arc::make_mut(&mut self.type_aliases).load_context_by_name(&context_name) {
                    Some(Ok(args)) => return Some(args),
                    Some(Err(e)) => {
                        log::warn!("Failed to parse context stubs for '{context_name}': {e}");
                        return None;
                    }
                    None => {
                        log::warn!("Unknown context name: '{context_name}'");
                        return None;
                    }
                }
            }
        }
        None
    }
}
