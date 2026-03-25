pub mod aliases;
mod builtins;
pub(crate) mod collect;
mod constrain;
pub mod coordinator;
pub mod diagnostic;
pub mod file_graph;
pub mod imports;
mod infer;
pub use infer::rss_mb;
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
use infer_expr::{PendingHasField, PendingMerge, PendingOverload, PendingWithFallback};
use la_arena::ArenaMap;
use lang_ast::{AstDb, Expr, ExprId, Module, NameId, NameResolution, NixFile, OverloadBinOp};
use lang_ty::{OutputTy, OwnedTy, PrimitiveTy, Ty, TyRef, TypeArena};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use thiserror::Error;
use tracing::instrument;
use type_table::TypeTable;

/// Extract type alias declarations from a Module's doc comments.
/// Returns a map of alias name → ParsedTy body. These are the types that
/// other files can import via `import("./path.nix").TypeName`.
pub fn extract_type_exports(module: &lang_ast::Module) -> HashMap<smol_str::SmolStr, ParsedTy> {
    let mut exports = HashMap::new();
    for alias_source in &module.inline_type_aliases {
        if let Some((name, body)) = comment_parser::parse_inline_type_alias(alias_source) {
            exports.insert(name, body);
        }
    }
    exports
}

/// Load inline type aliases from doc comments, applying CoW on the registry.
/// Most files have no inline aliases, so the Arc is shared without cloning.
fn load_inline_aliases(
    aliases: Arc<TypeAliasRegistry>,
    module: &lang_ast::Module,
) -> Arc<TypeAliasRegistry> {
    if module.inline_type_aliases.is_empty() {
        aliases
    } else {
        let mut cloned = (*aliases).clone();
        for alias_source in &module.inline_type_aliases {
            if let Some((name, body)) = comment_parser::parse_inline_type_alias(alias_source) {
                cloned.load_inline_alias(name, body);
            }
        }
        Arc::new(cloned)
    }
}

#[instrument(level = "info", skip_all, name = "check_file", fields(file = lang_ast::display_path(&file.path(db)).as_str()))]
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
    // This is the boundary where the one clone happens for callers that don't
    // already hold an Arc. All downstream functions share this Arc without cloning.
    check_file_with_imports(db, file, Arc::new(aliases.clone()), HashMap::new())
}

/// Type-check a file with pre-loaded aliases and pre-resolved import types.
pub fn check_file_with_imports(
    db: &dyn AstDb,
    file: NixFile,
    aliases: Arc<TypeAliasRegistry>,
    import_types: HashMap<ExprId, OwnedTy>,
) -> Result<InferenceResult, Box<TixDiagnostic>> {
    let module = lang_ast::module(db, file);
    let name_res = lang_ast::name_resolution(db, file);
    let indices = lang_ast::module_indices(db, file);
    let grouped_defs = lang_ast::group_def(db, file);

    let aliases = load_inline_aliases(aliases, &module);

    let check = CheckCtx::new(
        &module,
        &name_res,
        &indices.binding_expr,
        aliases,
        import_types,
        Arc::default(),
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

#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub arena: Arc<TypeArena>,
    pub name_ty_map: ArenaMap<NameId, TyRef>,
    pub expr_ty_map: ArenaMap<ExprId, TyRef>,
    /// Entry expression type with co-occurring variable preservation.
    /// Used by `extract_file_signature` for cross-file polymorphism.
    /// `None` when no co-occurring variables were detected (use expr_ty_map).
    pub file_sig_ty: Option<TyRef>,
}

impl PartialEq for InferenceResult {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.arena, &other.arena)
            && self.name_ty_map == other.name_ty_map
            && self.expr_ty_map == other.expr_ty_map
    }
}
impl Eq for InferenceResult {}

impl InferenceResult {
    pub fn ty_for_name(&self, name: NameId) -> Option<TyRef> {
        self.name_ty_map.get(name).copied()
    }

    pub fn ty_for_expr(&self, expr: ExprId) -> Option<TyRef> {
        self.expr_ty_map.get(expr).copied()
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
    /// Doc comment type annotation failed to parse.
    AnnotationParseError {
        name: smol_str::SmolStr,
        error: smol_str::SmolStr,
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
            Warning::AnnotationParseError { name, error } => {
                write!(f, "type annotation for `{name}` failed to parse: {error}")
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
    /// Whether inference was aborted due to memory pressure (RSS limit).
    /// Consumers can use this to emit a user-visible diagnostic.
    pub bailed_out: bool,
}

// ==============================================================================
// Cross-file inference types
// ==============================================================================

/// The externally-visible type of a Nix file: its root expression's OutputTy.
/// Stored in the `InferenceCoordinator` cache so that importers can resolve
/// cross-file types without re-inferring the dependency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileSignature {
    pub root_ty: OwnedTy,
}

/// Pre-import syntax data: everything needed for inference except resolved
/// import types (which the coordinator provides from its cache). Produced by
/// a `SyntaxProvider` implementation (CLI or LSP).
#[derive(Clone)]
pub struct SyntaxBundle {
    pub path: std::path::PathBuf,
    pub module: Module,
    pub module_indices: lang_ast::ModuleIndices,
    pub name_res: NameResolution,
    pub grouped_defs: lang_ast::GroupedDefs,
    pub registry: Arc<TypeAliasRegistry>,
    pub context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
}

// ==============================================================================
// InferenceInputs: precomputed data for running inference off the Salsa DB
// ==============================================================================

/// Everything needed to run type inference after the syntax phase (parse, lower,
/// nameres, SCC grouping). This bundle is `Send + Sync` so inference can run on
/// a thread pool without holding the Salsa database lock.
///
/// Shared between the CLI (parallel multi-file check) and the LSP (which wraps
/// this in `LspInferenceInputs` with additional presentation fields).
pub struct InferenceInputs {
    pub module: Module,
    pub module_indices: lang_ast::ModuleIndices,
    pub name_res: NameResolution,
    pub grouped_defs: lang_ast::GroupedDefs,
    pub registry: Arc<TypeAliasRegistry>,
    pub import_types: HashMap<ExprId, OwnedTy>,
    pub import_diagnostics: Vec<TixDiagnostic>,
    pub context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    /// RSS limit in MB. When process RSS exceeds this, inference bails out
    /// with partial results to avoid OOM from RLIMIT_AS. `None` means no
    /// RSS-based limit (CLI default).
    pub rss_limit_mb: Option<f64>,
    /// File path for tracing span context. `None` is fine — the span field
    /// will just be omitted.
    pub file_path: Option<std::path::PathBuf>,
}

/// Run type inference using precomputed syntax data. Does not need the Salsa
/// database. Consolidates the bail-out diagnostic logic shared by CLI and LSP.
#[instrument(level = "info", skip_all, name = "run_inference", fields(file = inputs.file_path.as_deref().map(lang_ast::display_path).unwrap_or_default().as_str()))]
pub fn run_inference(inputs: &InferenceInputs) -> CheckResult {
    let mut check_result = CheckBuilder::from_inputs(inputs).run();

    // Merge import diagnostics.
    check_result
        .diagnostics
        .extend(inputs.import_diagnostics.clone());

    // If inference bailed out (RSS limit), add diagnostic.
    if check_result.bailed_out {
        let missing_bindings: Vec<smol_str::SmolStr> = inputs
            .module
            .names()
            .filter(|(_, name)| {
                matches!(
                    name.kind,
                    lang_ast::NameKind::LetIn
                        | lang_ast::NameKind::RecAttrset
                        | lang_ast::NameKind::PlainAttrset
                )
            })
            .filter(|(id, _)| {
                check_result
                    .inference
                    .as_ref()
                    .is_none_or(|inf| inf.name_ty_map.get(*id).is_none())
            })
            .map(|(_, name)| name.text.clone())
            .collect();
        check_result.diagnostics.push(TixDiagnostic {
            at_expr: inputs.module.entry_expr,
            kind: diagnostic::TixDiagnosticKind::InferenceAborted { missing_bindings },
        });
    }

    check_result
}

/// Extract a compacted `FileSignature` from a `CheckResult`. Returns `None`
/// if inference failed or the root expression has no type.
///
/// This is the shared logic used by both `tix check` (CLI) and the LSP batch
/// warmup to build the `OwnedTy` that gets cached in `InferenceCoordinator`.
pub fn extract_file_signature(
    check_result: &CheckResult,
    entry_expr: lang_ast::ExprId,
) -> Option<FileSignature> {
    check_result.inference.as_ref().and_then(|inf| {
        // Prefer the co-occurring-aware file signature type when available.
        // This preserves polymorphism for cross-file function signatures
        // (e.g., `{ param ? null }: param` exports as `{ param?: a } -> a | null`).
        let root_ref = inf
            .file_sig_ty
            .or_else(|| inf.expr_ty_map.get(entry_expr).copied())?;
        Some(FileSignature {
            root_ty: OwnedTy::new(inf.arena.clone(), root_ref).compact(),
        })
    })
}

// ==============================================================================
// CheckBuilder: extensible entry point for error-collecting type inference
// ==============================================================================
//
// Replaces `check_file_collecting`, `check_file_collecting_with_cancel`, and
// `check_with_precomputed` with a single builder type. Adding a new option
// (e.g. ExprCanonMode) only requires adding one field + one setter method.

/// Builder for error-collecting type inference. Always returns partial results
/// — even when errors occur, bindings inferred before the error have types
/// available (e.g. for LSP hover).
pub struct CheckBuilder {
    module: Module,
    name_res: NameResolution,
    indices: lang_ast::ModuleIndices,
    grouped_defs: lang_ast::GroupedDefs,
    aliases: Arc<TypeAliasRegistry>,
    import_types: HashMap<ExprId, OwnedTy>,
    context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    rss_limit_mb: Option<f64>,
}

impl CheckBuilder {
    /// Create a builder by querying Salsa for syntax-phase results.
    pub fn from_db(
        db: &dyn AstDb,
        file: NixFile,
        aliases: Arc<TypeAliasRegistry>,
        import_types: HashMap<ExprId, OwnedTy>,
        context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    ) -> Self {
        Self {
            module: lang_ast::module(db, file),
            name_res: lang_ast::name_resolution(db, file),
            indices: lang_ast::module_indices(db, file),
            grouped_defs: lang_ast::group_def(db, file),
            aliases,
            import_types,
            context_args,
            rss_limit_mb: None,
        }
    }

    /// Create a builder from precomputed Salsa query results. Useful when
    /// the caller already holds owned copies (e.g. inference off the Salsa
    /// database lock in the LSP).
    pub fn from_precomputed(
        module: Module,
        name_res: NameResolution,
        indices: lang_ast::ModuleIndices,
        grouped_defs: lang_ast::GroupedDefs,
        aliases: Arc<TypeAliasRegistry>,
        import_types: HashMap<ExprId, OwnedTy>,
        context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    ) -> Self {
        Self {
            module,
            name_res,
            indices,
            grouped_defs,
            aliases,
            import_types,
            context_args,
            rss_limit_mb: None,
        }
    }

    /// Create a builder from an `InferenceInputs` bundle (used by
    /// `run_inference`).
    pub fn from_inputs(inputs: &InferenceInputs) -> Self {
        Self {
            module: inputs.module.clone(),
            name_res: inputs.name_res.clone(),
            indices: inputs.module_indices.clone(),
            grouped_defs: inputs.grouped_defs.clone(),
            aliases: Arc::clone(&inputs.registry),
            import_types: inputs.import_types.clone(),
            context_args: Arc::clone(&inputs.context_args),
            rss_limit_mb: inputs.rss_limit_mb,
        }
    }

    /// Set an RSS limit in MB for memory-pressure early exit.
    pub fn rss_limit(mut self, limit_mb: Option<f64>) -> Self {
        self.rss_limit_mb = limit_mb;
        self
    }

    /// Run type inference and return collected results + diagnostics.
    pub fn run(self) -> CheckResult {
        let aliases = load_inline_aliases(self.aliases, &self.module);

        let mut check = CheckCtx::new(
            &self.module,
            &self.name_res,
            &self.indices.binding_expr,
            aliases,
            self.import_types,
            self.context_args,
        );
        if let Some(limit) = self.rss_limit_mb {
            check = check.with_rss_limit(limit);
        }
        let (inference, mut diagnostics, bailed_out) = check.infer_prog_partial(self.grouped_defs);

        let lower_diags = diagnostic::lower_diagnostics_to_tix(
            &self.module.lower_diagnostics,
            self.module.entry_expr,
        );
        diagnostics.extend(lower_diags);

        CheckResult {
            inference: Some(inference),
            diagnostics,
            bailed_out,
        }
    }
}

/// A pending constraint that couldn't be resolved immediately because one or
/// both operand types are still unknown.
#[derive(Debug, Clone)]
pub enum PendingConstraint {
    Overload(PendingOverload),
    Merge(PendingMerge),
    HasField(PendingHasField),
    /// Multi-`with` fallback: at least one of the `with` environments must
    /// contain the requested field. Emitted when a name resolves through
    /// multiple nested `with` scopes.
    WithFallback(PendingWithFallback),
}

/// Constraints whose resolution is deferred until operand types are known.
#[derive(Debug, Clone, Default)]
pub struct DeferredConstraints {
    /// Active pending constraints for the current SCC group.
    pub active: Vec<PendingConstraint>,
    /// Overloads carried over from previous groups, keyed by the name they
    /// were generalized with. During extrusion, only overloads for the name
    /// being instantiated are re-instantiated — changing growth from O(3^N)
    /// to O(N).
    pub carried: FxHashMap<lang_ast::NameId, Vec<PendingOverload>>,
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

    /// Errors from lambda pattern/body inference where we chose to continue
    /// with a best-effort type rather than abort. Collected alongside the
    /// normal errors at the end of inference.
    deferred_errors: Vec<LocatedError>,

    types: TypeTable,

    /// Maps generalized names to their polymorphic TyId.
    /// The TyId + variable levels encode the polymorphic scheme.
    poly_type_env: ArenaMap<NameId, TyId>,

    /// Constraints whose resolution is deferred until operand types are known.
    deferred: DeferredConstraints,

    /// Early-canonicalized types for names, captured at generalization time
    /// before use-site extrusions contaminate polymorphic variables with
    /// concrete bounds.
    early_canonical: ArenaMap<NameId, (TypeArena, TyRef)>,

    /// Type alias registry loaded from .tix declaration files.
    /// Wrapped in Arc for copy-on-write: most files share the registry
    /// without cloning; Arc::make_mut clones only when mutation is needed
    /// (inline aliases or context loading).
    type_aliases: Arc<TypeAliasRegistry>,

    /// Pre-computed types for resolved import expressions. When an Apply ExprId
    /// is in this map, its type comes from the imported file's root expression
    /// rather than from the generic `import :: a -> b` builtin signature.
    import_types: HashMap<ExprId, OwnedTy>,

    /// Context argument types for the root lambda (from `tix.toml` context
    /// configuration). Maps parameter names (e.g. "config", "lib", "pkgs") to
    /// their declared types. Applied only to the module's entry expression
    /// when it's a lambda with a pattern parameter.
    context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,

    /// Type narrowing overrides for the current branch scope.
    ///
    /// When inside an if-then-else branch where the condition narrows a
    /// variable's type (e.g. `if x == null`), this maps the variable's NameId
    /// to a branch-local TyId. Consulted in `infer_reference` before the
    /// normal name resolution path. Pushed/popped around branch inference.
    narrow_overrides: FxHashMap<NameId, TyId>,

    /// Names whose type annotations and context args were pre-applied before
    /// SCC groups (in `pre_apply_entry_lambda_annotations`). These names
    /// should be skipped during Lambda inference in `infer_root` to avoid
    /// double-applying the annotation.
    pre_annotated_params: FxHashSet<NameId>,

    /// Operation counter for periodic RSS checks. Incremented in
    /// constrain() (the main hotspot for cascading work). Checked every
    /// RSS_CHECK_INTERVAL operations to avoid excessive procfs reads.
    op_counter: u32,

    /// Set when an RSS check fires. Once set, constrain()
    /// returns Ok(()) immediately, infer_expr short-circuits to a fresh
    /// variable, and extrude returns the original type as-is.
    bailed_out: bool,

    /// Optional RSS limit in MB. When set, `should_bail()` periodically
    /// checks the process RSS and triggers early exit if it exceeds this
    /// threshold. This prevents OOM crashes from RLIMIT_AS by bailing out
    /// before virtual address space is exhausted (virtual >> RSS).
    rss_limit_mb: Option<f64>,

    /// Tracks which expressions have already been inferred. Prevents O(N²)
    /// re-evaluation of shared sub-expressions — e.g. `inherit (from) f1..fN`
    /// where `from` is referenced by N Select expressions.
    inferred_exprs: FxHashSet<ExprId>,

    /// Type exports from other files, keyed by (canonical path, type name).
    /// Populated by the coordinator for files that declare types via
    /// `/** type Foo = ...; */` doc comments. Used to resolve
    /// `import("./path.nix").TypeName` in type annotations.
    imported_type_exports: HashMap<PathBuf, HashMap<smol_str::SmolStr, ParsedTy>>,

    /// Base directory for resolving relative import paths in type annotations.
    file_base_dir: Option<PathBuf>,

    /// Inferred root types of other files, for resolving `typeof import("path")`.
    /// Populated by the coordinator from FileSignature results.
    typeof_import_types: HashMap<PathBuf, OwnedTy>,
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
        type_aliases: Arc<TypeAliasRegistry>,
        import_types: HashMap<ExprId, OwnedTy>,
        context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    ) -> Self {
        Self {
            module,
            name_res,
            binding_exprs,
            current_expr: module.entry_expr,
            warnings: Vec::new(),
            deferred_errors: Vec::new(),
            types: TypeTable::with_capacity(module.names().len() + module.exprs().len()),
            poly_type_env: ArenaMap::new(),
            deferred: DeferredConstraints::default(),
            early_canonical: ArenaMap::new(),
            type_aliases,
            import_types,
            context_args,
            narrow_overrides: FxHashMap::default(),
            pre_annotated_params: FxHashSet::default(),
            op_counter: 0,
            bailed_out: false,
            rss_limit_mb: None,
            inferred_exprs: FxHashSet::default(),
            imported_type_exports: HashMap::new(),
            file_base_dir: None,
            typeof_import_types: HashMap::new(),
        }
    }

    /// Set imported type exports for cross-file type import resolution.
    pub fn with_imported_type_exports(
        mut self,
        exports: HashMap<PathBuf, HashMap<smol_str::SmolStr, ParsedTy>>,
    ) -> Self {
        self.imported_type_exports = exports;
        self
    }

    /// Set the base directory for resolving relative paths in type imports.
    pub fn with_file_base_dir(mut self, dir: PathBuf) -> Self {
        self.file_base_dir = Some(dir);
        self
    }

    /// Set inferred file types for resolving `typeof import("path")`.
    pub fn with_typeof_import_types(mut self, types: HashMap<PathBuf, OwnedTy>) -> Self {
        self.typeof_import_types = types;
        self
    }

    /// Set an RSS limit in MB. When RSS exceeds this threshold, inference
    /// bails out with partial results. Used by the LSP to prevent OOM
    /// crashes from RLIMIT_AS.
    pub fn with_rss_limit(mut self, limit_mb: f64) -> Self {
        self.rss_limit_mb = Some(limit_mb);
        self
    }

    /// How often (in constrain ops) to check RSS. `/proc/self/statm` is a
    /// procfs read so we don't want to do it on every constrain call.
    const RSS_CHECK_INTERVAL: u32 = 4096;

    /// Check whether inference should bail out due to memory pressure.
    /// Caches a positive result in `bailed_out` so subsequent checks are O(1).
    fn should_bail(&mut self) -> bool {
        if self.bailed_out {
            return true;
        }
        if let Some(limit) = self.rss_limit_mb {
            if self.op_counter.is_multiple_of(Self::RSS_CHECK_INTERVAL) {
                let rss = infer::rss_mb();
                if rss > limit {
                    log::warn!(
                        "RSS limit exceeded during inference: {:.0}MB > {:.0}MB limit, bailing out",
                        rss,
                        limit,
                    );
                    self.bailed_out = true;
                    return true;
                }
            }
        }
        false
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

    /// Intern an OwnedTy as a single frozen TyId. Instead of eagerly
    /// converting the entire type tree into TyIds (O(N) allocations),
    /// wraps it in `Ty::Frozen(OwnedTy)` — one allocation. Fields are
    /// materialized on demand when `constrain` encounters the Frozen type.
    fn intern_frozen_owned_ty(&mut self, owned: &OwnedTy) -> TyId {
        self.alloc_concrete(Ty::Frozen(owned.clone()))
    }

    /// Intern an OwnedTy into this file's TypeStorage, creating fresh TyIds.
    ///
    /// Each TyVar(n) in the OwnedTy maps to a fresh variable (via a local
    /// HashMap). This ensures imported types are fully isolated from the
    /// source file's TypeStorage — constraints applied in this file cannot
    /// propagate back to the imported file.
    fn intern_output_ty(&mut self, owned: &OwnedTy) -> TyId {
        let mut var_map: HashMap<u32, TyId> = HashMap::new();
        let mut ref_cache: HashMap<TyRef, TyId> = HashMap::new();
        self.intern_output_ty_inner(&owned.arena, owned.root, &mut var_map, &mut ref_cache)
    }

    fn intern_output_ty_inner(
        &mut self,
        arena: &TypeArena,
        ty: TyRef,
        var_map: &mut HashMap<u32, TyId>,
        ref_cache: &mut HashMap<TyRef, TyId>,
    ) -> TyId {
        // Preserve DAG sharing: if we already interned this TyRef, reuse it.
        // Without this, shared subtrees in the TypeArena expand exponentially
        // (e.g. common.nix's output type caused a 1.5GB allocation on chromium).
        if let Some(&cached) = ref_cache.get(&ty) {
            return cached;
        }

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
    fn apply_type_annotation(&mut self, name_id: NameId, ty: TyId) -> Result<(), LocatedError> {
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
    fn propagate_annotation_bounds(&mut self, annotation_ty: TyId, name_id: NameId) {
        let Some(&expr_id) = self.binding_exprs.get(&name_id) else {
            return;
        };
        self.propagate_annotation_bounds_inner(annotation_ty, expr_id);
    }

    fn propagate_annotation_bounds_inner(&mut self, annotation_ty: TyId, expr_id: ExprId) {
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
    fn resolve_type_operators(&self, ty: &ParsedTy) -> ParsedTy {
        self.resolve_type_operators_inner(ty, 0)
    }

    fn resolve_type_operators_inner(&self, ty: &ParsedTy, depth: usize) -> ParsedTy {
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
    fn expand_parsed_aliases(&self, ty: &ParsedTy, depth: usize) -> ParsedTy {
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
    fn intern_fresh_ty(&mut self, ty: ParsedTy) -> TyId {
        // Pre-resolve type operators (Param, Return, FieldAccess) at the
        // ParsedTy level before interning. This expands aliases and
        // destructures types so the result is a plain ParsedTy.
        let ty = self.resolve_type_operators(&ty);

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
                            let inner_id = self.intern_fresh_ty(alias_body);
                            let name = smol_str::SmolStr::from(ref_name.as_str());
                            self.alloc_concrete(Ty::Named(name, inner_id))
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
            // Union annotations: build a concrete Ty::Union tree instead of a
            // variable with lower bounds. This keeps types like `path | string`
            // fully concrete, which lets the extrusion short-circuit fire for
            // parent types (e.g. Derivation, Pkgs) that contain union fields.
            // Semantics are equivalent: constrain(Union(a,b), T) distributes to
            // constrain(a, T) ∧ constrain(b, T), same as the old variable approach.
            ParsedTy::Union(members) => {
                let tys: Vec<TyId> = members
                    .iter()
                    .map(|m| self.intern_parsed_ty(&m.0, substitutions))
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
                    .map(|m| self.intern_parsed_ty(&m.0, substitutions))
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
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions);
                self.extract_param_ty(inner_ty)
            }
            ParsedTy::Return(inner) => {
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions);
                self.extract_return_ty(inner_ty)
            }
            ParsedTy::FieldAccess(inner, key) => {
                let inner_ty = self.intern_parsed_ty(&inner.0, substitutions);
                self.extract_field_ty(inner_ty, key)
            }

            // import("./path.nix").TypeName — resolve from imported type exports.
            ParsedTy::ImportType(path, name) => {
                if let Some(base) = &self.file_base_dir {
                    let resolved = base.join(path);
                    if let Some(exports) = self.imported_type_exports.get(&resolved) {
                        if let Some(alias_body) = exports.get(name.as_str()).cloned() {
                            return self.intern_fresh_ty(alias_body);
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
    fn extract_param_ty(&mut self, ty: TyId) -> TyId {
        match self.types.storage.get(ty).clone() {
            crate::storage::TypeEntry::Concrete(Ty::Lambda { param, .. }) => param,
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                self.extract_param_ty(inner)
            }
            _ => self.new_var(), // Not a function — degrade
        }
    }

    /// Extract the return type from a TyId that should be a Lambda.
    fn extract_return_ty(&mut self, ty: TyId) -> TyId {
        match self.types.storage.get(ty).clone() {
            crate::storage::TypeEntry::Concrete(Ty::Lambda { body, .. }) => body,
            crate::storage::TypeEntry::Concrete(Ty::Named(_, inner)) => {
                self.extract_return_ty(inner)
            }
            _ => self.new_var(),
        }
    }

    /// Extract a field's type from a TyId that should be an AttrSet.
    fn extract_field_ty(&mut self, ty: TyId, key: &str) -> TyId {
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
