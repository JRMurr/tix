pub mod aliases;
mod builtins;
pub(crate) mod collect;
mod constrain;
pub mod diagnostic;
pub mod imports;
mod infer;
pub(crate) mod infer_expr;
mod narrow;
mod operators;
pub(crate) mod storage;
pub(crate) mod type_table;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod pbt;

use aliases::TypeAliasRegistry;
use comment_parser::{parse_and_collect, parse_context_annotation, ParsedTy, TypeVarValue};
use derive_more::Debug;
use diagnostic::TixDiagnostic;
use infer_expr::{PendingHasField, PendingMerge, PendingOverload};
use la_arena::ArenaMap;
use lang_ast::{AstDb, Expr, ExprId, Module, NameId, NameResolution, NixFile, OverloadBinOp};
use lang_ty::{OutputTy, PrimitiveTy, Ty};
use std::collections::{HashMap, HashSet};
use std::time::Instant;
use thiserror::Error;
use type_table::TypeTable;

#[salsa::tracked]
pub fn check_file(db: &dyn AstDb, file: NixFile) -> Result<InferenceResult, Box<TixDiagnostic>> {
    check_file_with_aliases(db, file, &TypeAliasRegistry::default())
}

/// Type-check a file with a pre-loaded type alias registry from .tix stubs.
/// Not a Salsa tracked function because `TypeAliasRegistry` is not Salsa-managed.
pub fn check_file_with_aliases(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
) -> Result<InferenceResult, Box<TixDiagnostic>> {
    check_file_with_imports(db, file, aliases, HashMap::new())
}

/// Type-check a file with pre-loaded aliases and pre-resolved import types.
pub fn check_file_with_imports(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
    import_types: HashMap<ExprId, OutputTy>,
) -> Result<InferenceResult, Box<TixDiagnostic>> {
    let module = lang_ast::module(db, file);
    let name_res = lang_ast::name_resolution(db, file);
    let indices = lang_ast::module_indices(db, file);
    let grouped_defs = lang_ast::group_def(db, file);
    let check = CheckCtx::new(
        &module,
        &name_res,
        &indices.binding_expr,
        aliases.clone(),
        import_types,
        HashMap::new(),
    );
    check.infer_prog(grouped_defs)
}

/// Tracks whether a type position is covariant (output/positive) or
/// contravariant (input/negative). Using an enum instead of `bool` prevents
/// silent sign-flip bugs where `polarity` is accidentally passed instead of
/// `!polarity`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Polarity {
    /// Output/covariant position — variables expand to union of lower bounds.
    Positive,
    /// Input/contravariant position — variables expand to intersection of upper bounds.
    Negative,
}

impl Polarity {
    pub fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
        }
    }

    pub fn is_positive(self) -> bool {
        matches!(self, Polarity::Positive)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
#[debug("TyId({_0:?})")]
pub struct TyId(u32);

impl From<u32> for TyId {
    #[inline]
    fn from(value: u32) -> Self {
        TyId(value)
    }
}

impl From<&u32> for TyId {
    #[inline]
    fn from(value: &u32) -> Self {
        TyId(*value)
    }
}

impl From<usize> for TyId {
    #[inline]
    fn from(value: usize) -> Self {
        u32::try_from(value).expect("TyId overflow").into()
    }
}

impl From<TyId> for usize {
    #[inline]
    fn from(value: TyId) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    pub name_ty_map: ArenaMap<NameId, OutputTy>,
    pub expr_ty_map: ArenaMap<ExprId, OutputTy>,
}

impl InferenceResult {
    pub fn ty_for_name(&self, name: NameId) -> Option<OutputTy> {
        self.name_ty_map.get(name).cloned()
    }

    pub fn ty_for_expr(&self, expr: ExprId) -> Option<OutputTy> {
        self.expr_ty_map.get(expr).cloned()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum InferenceError {
    #[error("Type mismatch: {:?} is not a subtype of {:?}", .0.0, .0.1)]
    TypeMismatch(Box<(Ty<TyId>, Ty<TyId>)>),

    #[error("Missing field: {field:?}")]
    MissingField {
        field: smol_str::SmolStr,
        available: Vec<smol_str::SmolStr>,
    },

    #[error("Can not do binary operation ({:?}) ({:?}) ({:?})", .0.0, .0.1, .0.2)]
    InvalidBinOp(Box<(OverloadBinOp, Ty<TyId>, Ty<TyId>)>),

    #[error("Can not do attrset merge on ({:?}) ({:?})", .0.0, .0.1)]
    InvalidAttrMerge(Box<(Ty<TyId>, Ty<TyId>)>),
}

/// A diagnostic payload paired with the expression where it occurred.
/// Used for both errors and warnings via type aliases below.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Located<T> {
    pub payload: T,
    /// The expression that was being inferred when the diagnostic occurred.
    pub at_expr: ExprId,
}

impl<T: std::fmt::Display> std::fmt::Display for Located<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.payload)
    }
}

impl<T: std::error::Error + 'static> std::error::Error for Located<T> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.payload)
    }
}

pub type LocatedError = Located<InferenceError>;
pub type LocatedWarning = Located<Warning>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Warning {
    UnresolvedName(smol_str::SmolStr),
    /// Doc comment annotation has a different number of arrows than the
    /// function's visible lambda parameters. The annotation is likely wrong
    /// (e.g. `foo :: string -> string` on a two-argument function).
    AnnotationArityMismatch {
        name: smol_str::SmolStr,
        annotation_arity: usize,
        expression_arity: usize,
    },
    /// Annotation present but body not verified against it. The declared
    /// type is trusted for callers.
    AnnotationUnchecked {
        name: smol_str::SmolStr,
        reason: smol_str::SmolStr,
    },
}

impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::UnresolvedName(name) => write!(f, "Unresolved name: {name}"),
            Warning::AnnotationArityMismatch {
                name,
                annotation_arity,
                expression_arity,
            } => write!(
                f,
                "annotation for `{name}` has arity {annotation_arity} but expression has {expression_arity} parameters; skipping"
            ),
            Warning::AnnotationUnchecked { name, reason } => {
                write!(f, "annotation for `{name}` accepted but not verified: {reason}")
            }
        }
    }
}

/// Partial inference results plus all collected diagnostics.
/// Allows the LSP to report diagnostics even when inference fails partway.
#[derive(Debug, Clone)]
pub struct CheckResult {
    /// If inference succeeded, contains the full result. If it failed, this is
    /// None (future: partial results from error recovery).
    pub inference: Option<InferenceResult>,
    /// Display-ready diagnostics (errors + warnings) with human-readable type
    /// names via OutputTy.
    pub diagnostics: Vec<TixDiagnostic>,
}

/// Type-check a file, collecting errors instead of aborting on the first one.
/// Always returns partial inference results — even when errors occur, bindings
/// that were successfully inferred before the error will have types available
/// (e.g. for LSP hover).
pub fn check_file_collecting(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
    import_types: HashMap<ExprId, OutputTy>,
    context_args: HashMap<smol_str::SmolStr, ParsedTy>,
) -> CheckResult {
    let module = lang_ast::module(db, file);
    let name_res = lang_ast::name_resolution(db, file);
    let indices = lang_ast::module_indices(db, file);
    let grouped_defs = lang_ast::group_def(db, file);
    let check = CheckCtx::new(
        &module,
        &name_res,
        &indices.binding_expr,
        aliases.clone(),
        import_types,
        context_args,
    );
    let (inference, diagnostics) = check.infer_prog_partial(grouped_defs);
    CheckResult {
        inference: Some(inference),
        diagnostics,
    }
}

/// A pending constraint that couldn't be resolved immediately because one or
/// both operand types are still unknown.
#[derive(Debug, Clone)]
pub enum PendingConstraint {
    Overload(PendingOverload),
    Merge(PendingMerge),
    HasField(PendingHasField),
}

/// Constraints whose resolution is deferred until operand types are known.
#[derive(Debug, Clone, Default)]
pub struct DeferredConstraints {
    /// Active pending constraints for the current SCC group.
    pub active: Vec<PendingConstraint>,
    /// Overloads carried over from previous groups — re-instantiated per
    /// call-site during extrusion.
    pub carried: Vec<PendingOverload>,
}

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    /// Maps names to their binding expressions (RHS of `let x = expr`,
    /// `inherit (env) x`, etc.). Used by narrowing analysis to trace
    /// through local aliases to recognize builtin calls like
    /// `let isString = builtins.isString`.
    binding_exprs: &'db HashMap<NameId, ExprId>,

    /// The expression currently being inferred. Updated at the top of
    /// `infer_expr` so that errors from `constrain()` or sub-calls are
    /// attributed to the correct source location.
    current_expr: ExprId,

    /// Warnings accumulated during inference (e.g. unresolved names).
    warnings: Vec<LocatedWarning>,

    types: TypeTable,

    /// Maps generalized names to their polymorphic TyId.
    /// The TyId + variable levels encode the polymorphic scheme.
    poly_type_env: ArenaMap<NameId, TyId>,

    /// Constraints whose resolution is deferred until operand types are known.
    deferred: DeferredConstraints,

    /// Early-canonicalized types for names, captured at generalization time
    /// before use-site extrusions contaminate polymorphic variables with
    /// concrete bounds.
    early_canonical: ArenaMap<NameId, OutputTy>,

    /// Type alias registry loaded from .tix declaration files.
    type_aliases: TypeAliasRegistry,

    /// Pre-computed types for resolved import expressions. When an Apply ExprId
    /// is in this map, its type comes from the imported file's root expression
    /// rather than from the generic `import :: a -> b` builtin signature.
    import_types: HashMap<ExprId, OutputTy>,

    /// Tracks which TyIds originated from type alias resolution. When a
    /// TypeVarValue::Reference is resolved to an alias body in intern_fresh_ty,
    /// or a Named OutputTy is interned, the resulting TyId is recorded here
    /// with the alias name. Used during canonicalization to wrap the result in
    /// OutputTy::Named so hover display shows the alias name instead of the
    /// fully expanded structural type.
    alias_provenance: HashMap<TyId, smol_str::SmolStr>,

    /// Context argument types for the root lambda (from `tix.toml` context
    /// configuration). Maps parameter names (e.g. "config", "lib", "pkgs") to
    /// their declared types. Applied only to the module's entry expression
    /// when it's a lambda with a pattern parameter.
    context_args: HashMap<smol_str::SmolStr, ParsedTy>,

    /// Type narrowing overrides for the current branch scope.
    ///
    /// When inside an if-then-else branch where the condition narrows a
    /// variable's type (e.g. `if x == null`), this maps the variable's NameId
    /// to a branch-local TyId. Consulted in `infer_reference` before the
    /// normal name resolution path. Pushed/popped around branch inference.
    narrow_overrides: HashMap<NameId, TyId>,

    /// Names whose type annotations and context args were pre-applied before
    /// SCC groups (in `pre_apply_entry_lambda_annotations`). These names
    /// should be skipped during Lambda inference in `infer_root` to avoid
    /// double-applying the annotation.
    pre_annotated_params: HashSet<NameId>,

    /// Optional deadline for inference. Checked after each SCC group and
    /// periodically during expression inference; if exceeded, remaining work
    /// is skipped and partial results returned. Used by import resolution to
    /// prevent a single file from blocking the LSP indefinitely.
    deadline: Option<Instant>,

    /// Expression counter for periodic deadline checks within infer_expr.
    /// Calling Instant::now() on every expression would be too expensive,
    /// so we only check every DEADLINE_CHECK_INTERVAL expressions.
    expr_counter: u32,

    /// Set when a periodic deadline check fires inside infer_expr. Once set,
    /// all subsequent infer_expr calls short-circuit to a fresh variable.
    deadline_exceeded: bool,
}

/// Count the function arity (number of arrows along the spine) of a ParsedTy.
/// For example, `a -> b -> c` has arity 2, and `int` has arity 0.
fn parsed_ty_arity(ty: &ParsedTy) -> usize {
    match ty {
        ParsedTy::Lambda { body, .. } => 1 + parsed_ty_arity(&body.0),
        _ => 0,
    }
}

/// Nixpkgs doc comments conventionally use uppercase primitive names
/// (`String`, `Bool`, `Int`, etc.) while Tix's grammar only recognizes
/// lowercase. Map the common uppercase variants to their primitive type
/// so annotations like `foo :: String -> Bool` work without requiring
/// explicit type aliases in stubs.
fn uppercase_primitive_alias(name: &str) -> Option<PrimitiveTy> {
    match name {
        "String" => Some(PrimitiveTy::String),
        "Bool" => Some(PrimitiveTy::Bool),
        "Int" => Some(PrimitiveTy::Int),
        "Float" => Some(PrimitiveTy::Float),
        "Path" => Some(PrimitiveTy::Path),
        "Null" => Some(PrimitiveTy::Null),
        "Number" => Some(PrimitiveTy::Number),
        _ => None,
    }
}

impl<'db> CheckCtx<'db> {
    pub fn new(
        module: &'db Module,
        name_res: &'db NameResolution,
        binding_exprs: &'db HashMap<NameId, ExprId>,
        type_aliases: TypeAliasRegistry,
        import_types: HashMap<ExprId, OutputTy>,
        context_args: HashMap<smol_str::SmolStr, ParsedTy>,
    ) -> Self {
        Self {
            module,
            name_res,
            binding_exprs,
            current_expr: module.entry_expr,
            warnings: Vec::new(),
            types: TypeTable::new(),
            poly_type_env: ArenaMap::new(),
            deferred: DeferredConstraints::default(),
            early_canonical: ArenaMap::new(),
            type_aliases,
            import_types,
            alias_provenance: HashMap::new(),
            context_args,
            narrow_overrides: HashMap::new(),
            pre_annotated_params: HashSet::new(),
            deadline: None,
            expr_counter: 0,
            deadline_exceeded: false,
        }
    }

    /// Set a deadline after which inference will bail out with partial results.
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Check whether the inference deadline has been exceeded.
    fn past_deadline(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() > d)
    }

    /// Allocate a fresh type variable at the current level.
    fn new_var(&mut self) -> TyId {
        self.types.new_var()
    }

    /// Allocate a concrete type and return its TyId.
    fn alloc_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        self.types.alloc_concrete(ty)
    }

    /// Allocate a primitive type, deduplicating via cache.
    fn alloc_prim(&mut self, prim: PrimitiveTy) -> TyId {
        self.types.alloc_prim(prim)
    }

    /// Count the number of visible nested lambda parameters in an expression.
    /// For `x: y: body`, this returns 2. For a non-lambda, returns 0.
    fn expr_lambda_arity(&self, expr: ExprId) -> usize {
        match &self.module[expr] {
            Expr::Lambda { body, .. } => 1 + self.expr_lambda_arity(*body),
            _ => 0,
        }
    }

    /// Get the pre-allocated TyId for a name (used during inference of the name's
    /// own definition, before it has been generalized).
    fn ty_for_name_direct(&self, name: NameId) -> TyId {
        let id: TyId = u32::from(name.into_raw()).into();
        debug_assert!(
            usize::from(id) < self.types.storage.len(),
            "ty_for_name_direct: TyId {id:?} out of bounds (storage has {} entries)",
            self.types.storage.len()
        );
        id
    }

    /// Get the pre-allocated TyId for an expression.
    fn ty_for_expr(&self, i: ExprId) -> TyId {
        let idx = self.module.names().len() as u32 + u32::from(i.into_raw());
        let id: TyId = idx.into();
        debug_assert!(
            usize::from(id) < self.types.storage.len(),
            "ty_for_expr: TyId {id:?} out of bounds (storage has {} entries)",
            self.types.storage.len()
        );
        id
    }

    /// Reverse of `ty_for_expr`: given a TyId, return the ExprId it was
    /// pre-allocated for, or None if the TyId is outside the expression range
    /// (i.e. it's a name slot or a dynamically created type).
    fn expr_for_ty(&self, ty: TyId) -> Option<ExprId> {
        let raw = ty.0;
        let names_len = self.module.names().len() as u32;
        let exprs_len = self.module.exprs().len() as u32;
        if raw >= names_len && raw < names_len + exprs_len {
            Some(ExprId::from_raw((raw - names_len).into()))
        } else {
            None
        }
    }

    // ==========================================================================
    // Type annotation interning (doc comment → internal types)
    // ==========================================================================

    // ==========================================================================
    // OutputTy interning (import results → internal types)
    // ==========================================================================

    /// Intern an OutputTy into this file's TypeStorage, creating fresh TyIds.
    ///
    /// Each TyVar(n) in the OutputTy maps to a fresh variable (via a local
    /// HashMap). This ensures imported types are fully isolated from the
    /// source file's TypeStorage — constraints applied in this file cannot
    /// propagate back to the imported file.
    fn intern_output_ty(&mut self, ty: &OutputTy) -> TyId {
        let mut var_map: HashMap<u32, TyId> = HashMap::new();
        self.intern_output_ty_inner(ty, &mut var_map)
    }

    fn intern_output_ty_inner(&mut self, ty: &OutputTy, var_map: &mut HashMap<u32, TyId>) -> TyId {
        match ty {
            OutputTy::TyVar(n) => *var_map.entry(*n).or_insert_with(|| self.new_var()),
            OutputTy::Primitive(prim) => self.alloc_prim(*prim),
            OutputTy::List(inner) => {
                let elem = self.intern_output_ty_inner(&inner.0, var_map);
                self.alloc_concrete(Ty::List(elem))
            }
            OutputTy::Lambda { param, body } => {
                let p = self.intern_output_ty_inner(&param.0, var_map);
                let b = self.intern_output_ty_inner(&body.0, var_map);
                self.alloc_concrete(Ty::Lambda { param: p, body: b })
            }
            OutputTy::AttrSet(attr) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let field_ty = self.intern_output_ty_inner(&v.0, var_map);
                    fields.insert(k.clone(), field_ty);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_output_ty_inner(&d.0, var_map));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                }))
            }
            // Union: create a fresh variable with each member as a lower bound.
            OutputTy::Union(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_output_ty_inner(&m.0, var_map);
                    self.constrain(member_ty, var)
                        .expect("union import constraint should not fail");
                }
                var
            }
            // Intersection: create a fresh variable with each member as an upper bound.
            OutputTy::Intersection(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_output_ty_inner(&m.0, var_map);
                    self.constrain(var, member_ty)
                        .expect("intersection import constraint should not fail");
                }
                var
            }
            // Named: intern the inner type and record the alias provenance on
            // the resulting TyId so canonicalization can re-wrap it.
            OutputTy::Named(name, inner) => {
                let ty_id = self.intern_output_ty_inner(&inner.0, var_map);
                self.alias_provenance.insert(ty_id, name.clone());
                ty_id
            }
            // Negation: intern the inner type and wrap in Ty::Neg.
            OutputTy::Neg(inner) => {
                let inner_id = self.intern_output_ty_inner(&inner.0, var_map);
                self.alloc_concrete(Ty::Neg(inner_id))
            }
            // Bottom (never): uninhabited type from contradictions. Intern as
            // a fresh variable with no bounds — it shouldn't appear in
            // importable type signatures in practice.
            OutputTy::Bottom => self.new_var(),
            // Top (any): universal type from tautologies. Intern as a fresh
            // unconstrained variable — equivalent to "any value" during
            // inference.
            OutputTy::Top => self.new_var(),
        }
    }

    /// If `name_id` has a doc comment type annotation (e.g. `/** type: x :: int */`),
    /// constrain `ty` to match the declared type. Returns Ok(()) if no annotation
    /// is present or if the constraint succeeds.
    fn apply_type_annotation(&mut self, name_id: NameId, ty: TyId) -> Result<(), LocatedError> {
        let type_annotation = self
            .module
            .type_dec_map
            .docs_for_name(name_id)
            .and_then(|docs| {
                let parsed: Vec<_> = docs
                    .iter()
                    .flat_map(|doc| parse_and_collect(doc).unwrap_or_default())
                    .collect();
                let name_str = &self.module[name_id].text;
                parsed.into_iter().find_map(|decl| {
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
                if let Some(name) = self.alias_provenance.get(&annotation_ty).cloned() {
                    self.alias_provenance.insert(ty, name);
                }
                // Propagate alias provenance through Lambda parameter structure.
                self.propagate_lambda_provenance(annotation_ty, name_id);
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
            if known_ty.contains_union() {
                // Still intern and record provenance for display purposes,
                // but don't apply constraints.
                let annotation_ty = self.intern_fresh_ty(known_ty);
                if let Some(name) = self.alias_provenance.get(&annotation_ty).cloned() {
                    self.alias_provenance.insert(ty, name);
                }
                // Propagate alias provenance through Lambda parameter structure
                // so that annotated param types (e.g. `BwrapArg`) display their
                // alias name instead of the expanded structural type.
                self.propagate_lambda_provenance(annotation_ty, name_id);
                return Ok(());
            }

            let annotation_ty = self.intern_fresh_ty(known_ty);
            self.constrain_equal(ty, annotation_ty)?;

            // Transfer alias provenance from the annotation to the expression
            // TyId so that early canonicalization wraps the name's type in
            // Named. Without this, the provenance lives only on annotation_ty
            // which early canonicalization never sees directly.
            if let Some(name) = self.alias_provenance.get(&annotation_ty).cloned() {
                self.alias_provenance.insert(ty, name);
            }
            // Propagate alias provenance through Lambda parameter structure
            // so that annotated param types display their alias name.
            self.propagate_lambda_provenance(annotation_ty, name_id);
        }

        Ok(())
    }

    /// Walk an interned annotation type and the corresponding expression in
    /// parallel, transferring alias provenance at each Lambda level.
    ///
    /// For `renderArg :: BwrapArg -> string`, the annotation creates a
    /// `Lambda { param, body }` where `param` has BwrapArg provenance. The
    /// expression is `Lambda { param: Some(name_id), body }`. We transfer
    /// provenance from the annotation's param TyId to the inferred param's
    /// TyId (derived from name_id) so that display shows "BwrapArg" instead
    /// of the fully expanded structural type.
    fn propagate_lambda_provenance(&mut self, annotation_ty: TyId, name_id: NameId) {
        let Some(&expr_id) = self.binding_exprs.get(&name_id) else {
            return;
        };
        self.propagate_lambda_provenance_inner(annotation_ty, expr_id);
    }

    fn propagate_lambda_provenance_inner(&mut self, annotation_ty: TyId, expr_id: ExprId) {
        // Get the annotation type structure.
        let annot_entry = self.types.storage.get(annotation_ty).clone();
        let (annot_param, annot_body) = match annot_entry {
            crate::storage::TypeEntry::Concrete(Ty::Lambda { param, body }) => (param, body),
            _ => return,
        };

        // Get the expression structure.
        let expr = self.module[expr_id].clone();
        let (param_name, body_expr) = match expr {
            Expr::Lambda { param, body, .. } => (param, body),
            _ => return,
        };

        // Transfer provenance from annotation param to inferred param.
        if let Some(param_name_id) = param_name {
            let inferred_param_ty = self.ty_for_name_direct(param_name_id);
            if let Some(name) = self.alias_provenance.get(&annot_param).cloned() {
                self.alias_provenance.insert(inferred_param_ty, name);
            }
        }

        // Recurse into the body: if the annotation body is also a Lambda,
        // walk into the body expression to transfer deeper provenance.
        self.propagate_lambda_provenance_inner(annot_body, body_expr);
    }

    /// Intern a ParsedTy with fresh type variables for each free generic var
    /// and alias resolution for Reference vars. Each call produces an independent
    /// "instance" — analogous to polymorphic instantiation.
    fn intern_fresh_ty(&mut self, ty: ParsedTy) -> TyId {
        let free_vars = ty.free_vars();

        let subs: HashMap<TypeVarValue, TyId> = free_vars
            .iter()
            .map(|var| {
                let ty_id = match var {
                    TypeVarValue::Generic(_) => self.new_var(),
                    TypeVarValue::Reference(ref_name) => {
                        // Resolve against loaded type aliases. If found,
                        // recursively intern the alias body (with its own
                        // fresh vars) to get a polymorphic instance.
                        if let Some(alias_body) = self.type_aliases.get(ref_name).cloned() {
                            let ty_id = self.intern_fresh_ty(alias_body);
                            self.alias_provenance
                                .insert(ty_id, smol_str::SmolStr::from(ref_name.as_str()));
                            ty_id
                        } else if let Some(prim) = uppercase_primitive_alias(ref_name) {
                            // Nixpkgs doc comments conventionally use uppercase
                            // primitive names (String, Bool, Int, etc.). Map them
                            // to the corresponding lowercase primitive type.
                            self.alloc_prim(prim)
                        } else {
                            // Unknown reference — degrade to fresh variable.
                            self.new_var()
                        }
                    }
                };
                (var.clone(), ty_id)
            })
            .collect();

        self.intern_parsed_ty(&ty, &subs)
    }

    fn intern_parsed_ty(
        &mut self,
        ty: &ParsedTy,
        substitutions: &HashMap<TypeVarValue, TyId>,
    ) -> TyId {
        match ty {
            ParsedTy::TyVar(var) => {
                // `Any` is treated as a wildcard — each occurrence gets its own
                // fresh variable so `Any -> Any` doesn't unify the two positions.
                // This matches the noogle convention where `Any` means "some type"
                // rather than "the same type everywhere".
                if let comment_parser::TypeVarValue::Reference(name) = var {
                    if name == "Any" && self.type_aliases.get("Any").is_none() {
                        return self.new_var();
                    }
                }
                let replacement = substitutions
                    .get(var)
                    .unwrap_or_else(|| panic!("No replacement for {var:?}"));
                *replacement
            }
            ParsedTy::Primitive(prim) => self.alloc_prim(*prim),
            ParsedTy::List(inner) => {
                let new_inner = self.intern_parsed_ty(&inner.0, substitutions);
                self.alloc_concrete(Ty::List(new_inner))
            }
            ParsedTy::Lambda { param, body } => {
                let new_param = self.intern_parsed_ty(&param.0, substitutions);
                let new_body = self.intern_parsed_ty(&body.0, substitutions);
                self.alloc_concrete(Ty::Lambda {
                    param: new_param,
                    body: new_body,
                })
            }
            ParsedTy::AttrSet(attr) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let new_v = self.intern_parsed_ty(&v.0, substitutions);
                    fields.insert(k.clone(), new_v);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_parsed_ty(&d.0, substitutions));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                }))
            }
            // Union annotations: create a fresh variable with each member as a lower bound.
            // This encodes `int | string` as a var where `int <: var` and `string <: var`.
            ParsedTy::Union(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(member_ty, var)
                        .expect("union annotation constraint should not fail");
                }
                var
            }
            // Intersection annotations: create a fresh variable with each member as an upper bound.
            // This encodes `a & b` as a var where `var <: a` and `var <: b`.
            ParsedTy::Intersection(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(var, member_ty)
                        .expect("intersection annotation constraint should not fail");
                }
                var
            }
        }
    }

    /// Wrap a bare `InferenceError` with the current expression location.
    fn locate_err(&self, err: InferenceError) -> LocatedError {
        Located {
            payload: err,
            at_expr: self.current_expr,
        }
    }

    /// Record a warning at the current expression.
    fn emit_warning(&mut self, warning: Warning) {
        self.warnings.push(Located {
            payload: warning,
            at_expr: self.current_expr,
        });
    }

    /// Check whether a lambda expression has a `/** context: <name> */` doc
    /// comment annotation. If so, load the named context's stubs and return
    /// the arg→type map.
    ///
    /// Results are NOT cached because context annotations are rare (typically
    /// one per file at most), and the cost of re-parsing is negligible compared
    /// to inference.
    fn resolve_doc_comment_context(
        &mut self,
        expr_id: ExprId,
    ) -> Option<HashMap<smol_str::SmolStr, ParsedTy>> {
        let docs = self.module.type_dec_map.docs_for_expr(expr_id)?;
        for doc in docs {
            if let Some(context_name) = parse_context_annotation(doc) {
                match self.type_aliases.load_context_by_name(&context_name) {
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
