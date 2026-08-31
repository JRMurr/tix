pub mod aliases;
mod annotations;
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
use comment_parser::{ParsedTy, TypeVarValue};
use derive_more::Debug;
use diagnostic::TixDiagnostic;
use infer_expr::{PendingHasField, PendingMerge, PendingOverload, PendingWithFallback};
use la_arena::ArenaMap;
use lang_ast::{Expr, ExprId, Module, NameId, NameResolution, OverloadBinOp};
use lang_ty::{OutputTy, OwnedTy, PrimitiveTy, Ty, TyRef, TypeArena};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::path::PathBuf;

use std::sync::Arc;
use thiserror::Error;
use tracing::instrument;
use type_table::TypeTable;

/// Extract type alias declarations from a Module's doc comments.
/// Returns a map of alias name → ParsedTy body. These are the types that
/// other files can import via `import("./path.nix").TypeName`.
pub fn extract_type_exports(module: &lang_ast::Module) -> HashMap<smol_str::SmolStr, ParsedTy> {
    let mut exports = HashMap::default();
    for alias_source in &module.inline_type_aliases {
        if let Some((name, body)) = comment_parser::parse_inline_type_alias(alias_source) {
            exports.insert(name, body);
        }
    }
    exports
}

/// For exported type aliases that contain `typeof varname`, return the
/// set of binding names whose types need to be inferred.
pub fn find_typeof_targets(
    exports: &HashMap<smol_str::SmolStr, ParsedTy>,
) -> HashSet<smol_str::SmolStr> {
    let mut targets = HashSet::default();
    for body in exports.values() {
        collect_typeof_names(body, &mut targets);
    }
    targets
}

fn collect_typeof_names(ty: &ParsedTy, out: &mut HashSet<smol_str::SmolStr>) {
    match ty {
        ParsedTy::TypeOf(name) => {
            out.insert(name.clone());
        }
        ParsedTy::Param(inner) | ParsedTy::Return(inner) | ParsedTy::FieldAccess(inner, _) => {
            collect_typeof_names(&inner.0, out);
        }
        ParsedTy::Lambda { param, body } => {
            collect_typeof_names(&param.0, out);
            collect_typeof_names(&body.0, out);
        }
        ParsedTy::List(inner) => {
            collect_typeof_names(&inner.0, out);
        }
        ParsedTy::AttrSet(attr) => {
            for val in attr.fields.values() {
                collect_typeof_names(&val.0, out);
            }
            if let Some(dyn_ty) = &attr.dyn_ty {
                collect_typeof_names(&dyn_ty.0, out);
            }
        }
        ParsedTy::Union(members) | ParsedTy::Intersection(members) => {
            for m in members {
                collect_typeof_names(&m.0, out);
            }
        }
        // Leaf variants: Primitive, TyVar, Top, Bottom, ImportType, TypeOfImport
        _ => {}
    }
}

/// Given a binding name and grouped defs, find the SCC group index
/// that contains the binding. Returns None if not found.
pub fn find_scc_group_for_name(
    module: &lang_ast::Module,
    groups: &lang_ast::GroupedDefs,
    name: &str,
) -> Option<usize> {
    for (i, group) in groups.iter().enumerate() {
        for def in group {
            if module[def.name()].text.as_str() == name {
                return Some(i);
            }
        }
    }
    None
}

/// Convert an `OwnedTy` (OutputTy in a TypeArena) to a `ParsedTy`.
///
/// This conversion is lossy: `Named` wrappers are discarded, `Neg` types
/// become `Top`, and type variable indices map to letter names (0→"a", etc.).
/// Sufficient for concrete types like attrset shapes.
pub fn owned_ty_to_parsed_ty(owned: &OwnedTy) -> ParsedTy {
    output_ty_to_parsed_ty(&owned.arena, owned.root)
}

fn output_ty_to_parsed_ty(arena: &lang_ty::TypeArena, ty_ref: TyRef) -> ParsedTy {
    use comment_parser::ParsedTyRef;

    match arena.get(ty_ref) {
        OutputTy::Primitive(p) => ParsedTy::Primitive(*p),
        OutputTy::TyVar(n) => {
            // Map variable index to a letter name: 0→"a", 1→"b", ...
            let letter = (b'a' + (*n as u8 % 26)) as char;
            ParsedTy::TyVar(TypeVarValue::Generic(smol_str::SmolStr::from(
                letter.to_string(),
            )))
        }
        OutputTy::List(inner) => {
            ParsedTy::List(ParsedTyRef::from(output_ty_to_parsed_ty(arena, *inner)))
        }
        OutputTy::Lambda { param, body } => ParsedTy::Lambda {
            param: ParsedTyRef::from(output_ty_to_parsed_ty(arena, *param)),
            body: ParsedTyRef::from(output_ty_to_parsed_ty(arena, *body)),
        },
        OutputTy::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        ParsedTyRef::from(output_ty_to_parsed_ty(arena, *v)),
                    )
                })
                .collect();
            let dyn_ty = attr
                .dyn_ty
                .map(|d| ParsedTyRef::from(output_ty_to_parsed_ty(arena, d)));
            ParsedTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }
        OutputTy::Union(members) => ParsedTy::Union(
            members
                .iter()
                .map(|m| ParsedTyRef::from(output_ty_to_parsed_ty(arena, *m)))
                .collect(),
        ),
        OutputTy::Intersection(members) => ParsedTy::Intersection(
            members
                .iter()
                .map(|m| ParsedTyRef::from(output_ty_to_parsed_ty(arena, *m)))
                .collect(),
        ),
        OutputTy::Named(_, inner) => output_ty_to_parsed_ty(arena, *inner),
        OutputTy::Neg(_) => ParsedTy::Top, // approximation
        OutputTy::Top => ParsedTy::Top,
        OutputTy::Bottom => ParsedTy::Bottom,
        OutputTy::Extern(ext) => owned_ty_to_parsed_ty(ext),
    }
}

/// Substitute `TypeOf(name)` nodes in exported `ParsedTy` trees with the
/// actual inferred types from `binding_types`. Unresolved `TypeOf` nodes
/// (name not in binding_types) are left as-is.
pub fn resolve_export_typeof(
    raw_exports: &HashMap<smol_str::SmolStr, ParsedTy>,
    binding_types: &HashMap<smol_str::SmolStr, OwnedTy>,
) -> HashMap<smol_str::SmolStr, ParsedTy> {
    raw_exports
        .iter()
        .map(|(name, body)| {
            (
                name.clone(),
                resolve_typeof_in_parsed_ty(body, binding_types),
            )
        })
        .collect()
}

fn resolve_typeof_in_parsed_ty(
    ty: &ParsedTy,
    binding_types: &HashMap<smol_str::SmolStr, OwnedTy>,
) -> ParsedTy {
    use comment_parser::ParsedTyRef;

    match ty {
        ParsedTy::TypeOf(name) => {
            if let Some(owned) = binding_types.get(name.as_str()) {
                owned_ty_to_parsed_ty(owned)
            } else {
                ty.clone()
            }
        }
        ParsedTy::Param(inner) => ParsedTy::Param(ParsedTyRef::from(resolve_typeof_in_parsed_ty(
            &inner.0,
            binding_types,
        ))),
        ParsedTy::Return(inner) => ParsedTy::Return(ParsedTyRef::from(
            resolve_typeof_in_parsed_ty(&inner.0, binding_types),
        )),
        ParsedTy::FieldAccess(inner, field) => ParsedTy::FieldAccess(
            ParsedTyRef::from(resolve_typeof_in_parsed_ty(&inner.0, binding_types)),
            field.clone(),
        ),
        ParsedTy::Lambda { param, body } => ParsedTy::Lambda {
            param: ParsedTyRef::from(resolve_typeof_in_parsed_ty(&param.0, binding_types)),
            body: ParsedTyRef::from(resolve_typeof_in_parsed_ty(&body.0, binding_types)),
        },
        ParsedTy::List(inner) => ParsedTy::List(ParsedTyRef::from(resolve_typeof_in_parsed_ty(
            &inner.0,
            binding_types,
        ))),
        ParsedTy::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        ParsedTyRef::from(resolve_typeof_in_parsed_ty(&v.0, binding_types)),
                    )
                })
                .collect();
            let dyn_ty = attr
                .dyn_ty
                .as_ref()
                .map(|d| ParsedTyRef::from(resolve_typeof_in_parsed_ty(&d.0, binding_types)));
            ParsedTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }
        ParsedTy::Union(members) => ParsedTy::Union(
            members
                .iter()
                .map(|m| ParsedTyRef::from(resolve_typeof_in_parsed_ty(&m.0, binding_types)))
                .collect(),
        ),
        ParsedTy::Intersection(members) => ParsedTy::Intersection(
            members
                .iter()
                .map(|m| ParsedTyRef::from(resolve_typeof_in_parsed_ty(&m.0, binding_types)))
                .collect(),
        ),
        // Leaf variants that don't contain TypeOf: pass through unchanged
        _ => ty.clone(),
    }
}

/// Run partial inference on SCC groups 0..=`stop_after_group` and return the
/// inferred types for `target_names` as portable `OwnedTy` values.
///
/// Used by the coordinator to get binding types for `typeof` references in
/// type exports without running full file inference.
pub fn run_partial_inference(
    inputs: &InferenceInputs,
    stop_after_group: usize,
    target_names: &HashSet<smol_str::SmolStr>,
) -> HashMap<smol_str::SmolStr, OwnedTy> {
    let aliases = load_inline_aliases(Arc::clone(&inputs.registry), &inputs.module);

    let check = CheckCtx::new(
        &inputs.module,
        &inputs.name_res,
        &inputs.module_indices.binding_expr,
        aliases,
        inputs.import_types.clone(),
        Arc::clone(&inputs.context_args),
    );

    let (result, _diagnostics) =
        check.infer_prog_up_to_group(inputs.grouped_defs.clone(), stop_after_group);

    let mut binding_types = HashMap::default();
    for (name_id, &ty_ref) in result.name_ty_map.iter() {
        let name_text = inputs.module[name_id].text.clone();
        if target_names.contains(name_text.as_str()) {
            binding_types.insert(
                name_text,
                OwnedTy::new(result.arena.clone(), ty_ref).compact(),
            );
        }
    }
    binding_types
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

/// Type-check Nix source from scratch (parses, lowers, resolves, infers).
/// Convenience for tests and simple callers.
pub fn check_source(src: &str) -> Result<InferenceResult, Box<TixDiagnostic>> {
    check_source_with_aliases(src, &TypeAliasRegistry::default())
}

/// Type-check Nix source with a pre-loaded type alias registry.
pub fn check_source_with_aliases(
    src: &str,
    aliases: &TypeAliasRegistry,
) -> Result<InferenceResult, Box<TixDiagnostic>> {
    let r = lang_ast::run_syntax_pipeline(src);
    let aliases = load_inline_aliases(Arc::new(aliases.clone()), &r.module);

    let check = CheckCtx::new(
        &r.module,
        &r.name_res,
        &r.module_indices.binding_expr,
        aliases,
        HashMap::default(),
        Arc::default(),
    );
    check.infer_prog(r.grouped_defs)
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
// InferenceInputs: precomputed data for running inference
// ==============================================================================

/// Everything needed to run type inference after the syntax phase (parse, lower,
/// nameres, SCC grouping). This bundle is `Send + Sync` so inference can run on
/// a thread pool.
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
    /// Type exports from other files, keyed by canonical path → name → ParsedTy.
    /// Populated by the coordinator when cross-file type imports are detected.
    pub imported_type_exports: HashMap<std::path::PathBuf, HashMap<smol_str::SmolStr, ParsedTy>>,
    /// Inferred root types of other files for `typeof import("path")`.
    pub typeof_import_types: HashMap<std::path::PathBuf, OwnedTy>,
    /// Base directory for resolving relative paths in type annotations.
    pub file_base_dir: Option<std::path::PathBuf>,
}

/// Run type inference using precomputed syntax data. Does not need the
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
    imported_type_exports: HashMap<PathBuf, HashMap<smol_str::SmolStr, ParsedTy>>,
    typeof_import_types: HashMap<PathBuf, OwnedTy>,
    file_base_dir: Option<PathBuf>,
}

impl CheckBuilder {
    /// Create a builder from Nix source text. Runs the full syntax pipeline.
    /// Convenience for tests and simple callers.
    pub fn from_source(
        src: &str,
        aliases: Arc<TypeAliasRegistry>,
        import_types: HashMap<ExprId, OwnedTy>,
        context_args: Arc<HashMap<smol_str::SmolStr, ParsedTy>>,
    ) -> Self {
        let r = lang_ast::run_syntax_pipeline(src);
        Self {
            module: r.module,
            name_res: r.name_res,
            indices: r.module_indices,
            grouped_defs: r.grouped_defs,
            aliases,
            import_types,
            context_args,
            rss_limit_mb: None,
            imported_type_exports: HashMap::default(),
            typeof_import_types: HashMap::default(),
            file_base_dir: None,
        }
    }

    /// Create a builder from precomputed syntax pipeline results.
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
            imported_type_exports: HashMap::default(),
            typeof_import_types: HashMap::default(),
            file_base_dir: None,
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
            imported_type_exports: inputs.imported_type_exports.clone(),
            typeof_import_types: inputs.typeof_import_types.clone(),
            file_base_dir: inputs.file_base_dir.clone(),
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
        if !self.imported_type_exports.is_empty() {
            check = check.with_imported_type_exports(self.imported_type_exports);
        }
        if let Some(dir) = self.file_base_dir {
            check = check.with_file_base_dir(dir);
        }
        if !self.typeof_import_types.is_empty() {
            check = check.with_typeof_import_types(self.typeof_import_types);
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

/// Identity of an alias being interned: a registry alias by name, or an
/// `import("./x.nix").T` export by file and name.

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

    /// Reusable scratch map for `extrude` — cleared per call, kept allocated.
    extrude_scratch: FxHashMap<TyId, TyId>,

    /// Early-canonicalized types for names, captured at generalization time
    /// before use-site extrusions contaminate polymorphic variables with
    /// concrete bounds.
    /// Arc so lambda pattern fields can share the function's arena instead of
    /// deep-copying it per field.
    early_canonical: ArenaMap<NameId, (Arc<TypeArena>, TyRef)>,

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
            extrude_scratch: FxHashMap::default(),
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
            imported_type_exports: HashMap::default(),
            file_base_dir: None,
            typeof_import_types: HashMap::default(),
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
            Expr::Lambda { body, .. } => {
                lang_ast::stack::with_stack(|| 1 + self.expr_lambda_arity(*body))
            }
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
}
