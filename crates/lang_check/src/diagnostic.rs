// ==============================================================================
// Display-Ready Diagnostics
// ==============================================================================
//
// TixDiagnostic is the public-facing error type. Type-bearing variants store
// `OwnedTy` (an arena + root index bundle) which carries its own display
// context and supports structural equality. Conversion from internal
// InferenceError happens at the inference/output boundary while TypeStorage
// is still available for canonicalization.

use std::fmt;
use std::sync::Arc;

use lang_ast::{AstPtr, Expr, ExprId, Module, OverloadBinOp};
use lang_ty::{DisplayConfig, OutputTy, OwnedTy, TypeArena};
use smol_str::SmolStr;

use crate::collect::canonicalize_standalone;
use crate::storage::TypeStorage;
use crate::{InferenceError, Located, LocatedError, LocatedWarning, Polarity, TyId, Warning};

// ==============================================================================
// DiagTy — arena-backed type with structural equality for diagnostics
// ==============================================================================
//
// `OwnedTy::PartialEq` uses pointer identity (same Arc + same root index).
// Diagnostics need structural equality so that an error produced by inference
// can be compared to an expected value constructed in a test. `DiagTy` wraps
// `OwnedTy` and compares by normalised display string, which is canonical for
// any structurally equal pair of types.

/// Arena-backed type wrapper for diagnostic fields.
///
/// Equality is structural: two `DiagTy` values are equal when their full
/// (unlimited) display strings match.  This allows diagnostic assertions
/// like `assert_eq!(error.kind, TixDiagnosticKind::TypeMismatch { ... })`
/// to work even when the two arenas are distinct allocations.
#[derive(Clone)]
pub struct DiagTy(pub OwnedTy);

impl DiagTy {
    /// Render with truncation for human-facing messages.
    pub fn display_truncated(&self, config: &DisplayConfig) -> String {
        self.0.display_truncated(config)
    }
}

impl PartialEq for DiagTy {
    fn eq(&self, other: &Self) -> bool {
        // Structural equality: compare the full (unlimited) display strings.
        // Two types are equal iff their canonical string representations match.
        let full = DisplayConfig::full();
        self.0.display_truncated(&full) == other.0.display_truncated(&full)
    }
}

impl Eq for DiagTy {}

impl fmt::Debug for DiagTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "DiagTy({})",
            self.0.display_truncated(&DisplayConfig::full())
        )
    }
}

/// A display-ready diagnostic paired with the expression where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TixDiagnostic {
    pub at_expr: ExprId,
    pub kind: TixDiagnosticKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TixDiagnosticKind {
    TypeMismatch {
        expected: DiagTy,
        actual: DiagTy,
        /// Optional hint for the user (e.g. suggesting path concatenation).
        hint: Option<String>,
    },
    MissingField {
        field: SmolStr,
        available_fields: Vec<SmolStr>,
        suggestion: Option<SmolStr>,
    },
    InvalidBinOp {
        op: OverloadBinOp,
        lhs_ty: DiagTy,
        rhs_ty: DiagTy,
    },
    InvalidAttrMerge {
        lhs_ty: DiagTy,
        rhs_ty: DiagTy,
    },
    UnresolvedName {
        name: SmolStr,
    },
    AnnotationArityMismatch {
        name: SmolStr,
        annotation_arity: usize,
        expression_arity: usize,
    },
    AnnotationUnchecked {
        name: SmolStr,
        reason: SmolStr,
    },
    /// Two bindings in the same attrset or let-block define the same key.
    /// Nix allows this (the second silently overwrites the first), but it
    /// is almost always a mistake.
    DuplicateKey {
        key: SmolStr,
        /// Syntax span of the first definition.
        first: AstPtr,
        /// Syntax span of the duplicate definition.
        second: AstPtr,
    },
    /// An imported file could not be found on disk.
    ImportNotFound {
        path: String,
    },
    /// A doc comment type annotation could not be parsed.
    AnnotationParseError {
        name: SmolStr,
        error: SmolStr,
    },
    /// Inference was aborted due to memory pressure (RSS limit exceeded).
    /// Bindings inferred before the limit was reached still have types;
    /// only the remaining ones are missing.
    InferenceAborted {
        /// Names of bindings that were not inferred before the abort.
        /// Empty if all bindings were inferred but expression-level types
        /// were skipped.
        missing_bindings: Vec<SmolStr>,
    },
    /// An angle bracket import (e.g. `import <nixpkgs>`) was encountered.
    /// These require NIX_PATH resolution which tix doesn't implement.
    AngleBracketImport {
        path: String,
    },
    /// An imported file exists but has no ephemeral stub (hasn't been
    /// analyzed). The resulting type is unconstrained (`?`).
    ImportUnresolved {
        path: String,
    },
    /// A type that cannot be used in Nix string interpolation (`"${expr}"`).
    /// Nix only supports interpolation for strings, paths, and derivations
    /// (attrsets with `outPath`). Types like int, bool, float, null, lists,
    /// and lambdas require an explicit `toString` call.
    InvalidInterpolation {
        actual: DiagTy,
    },
}

// ==============================================================================
// Diagnostic Error Codes
// ==============================================================================
//
// Every diagnostic has a stable error code (E001–E015) that appears in CLI
// output (`error[E001]: ...`) and as a clickable link in the LSP.  Once
// assigned, a code never changes meaning — new diagnostics get new codes.

const DOCS_BASE_URL: &str = "https://jrmurr.github.io/tix/diagnostics";

impl TixDiagnosticKind {
    /// Stable error code for this diagnostic kind.
    pub fn code(&self) -> &'static str {
        match self {
            TixDiagnosticKind::TypeMismatch { .. } => "E001",
            TixDiagnosticKind::MissingField { .. } => "E002",
            TixDiagnosticKind::InvalidBinOp { .. } => "E003",
            TixDiagnosticKind::InvalidAttrMerge { .. } => "E004",
            TixDiagnosticKind::UnresolvedName { .. } => "E005",
            TixDiagnosticKind::DuplicateKey { .. } => "E006",
            TixDiagnosticKind::ImportNotFound { .. } => "E007",
            TixDiagnosticKind::InferenceAborted { .. } => "E008",
            TixDiagnosticKind::AnnotationArityMismatch { .. } => "E009",
            TixDiagnosticKind::AnnotationUnchecked { .. } => "E010",
            TixDiagnosticKind::AnnotationParseError { .. } => "E011",
            TixDiagnosticKind::AngleBracketImport { .. } => "E012",
            TixDiagnosticKind::ImportUnresolved { .. } => "E013",
            TixDiagnosticKind::InvalidInterpolation { .. } => "E015",
        }
    }

    /// URL to the documentation page for this error code.
    pub fn docs_url(&self) -> String {
        let code = self.code().to_ascii_lowercase();
        format!("{DOCS_BASE_URL}/{code}.html")
    }

    /// Whether this diagnostic is a warning (true) or an error (false).
    pub fn is_warning(&self) -> bool {
        matches!(
            self,
            TixDiagnosticKind::UnresolvedName { .. }
                | TixDiagnosticKind::AnnotationArityMismatch { .. }
                | TixDiagnosticKind::AnnotationUnchecked { .. }
                | TixDiagnosticKind::AnnotationParseError { .. }
                | TixDiagnosticKind::DuplicateKey { .. }
                | TixDiagnosticKind::ImportNotFound { .. }
                | TixDiagnosticKind::InferenceAborted { .. }
                | TixDiagnosticKind::AngleBracketImport { .. }
                | TixDiagnosticKind::ImportUnresolved { .. }
        )
    }
}

impl fmt::Display for TixDiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dc = DisplayConfig::diagnostic();
        match self {
            TixDiagnosticKind::TypeMismatch {
                expected,
                actual,
                hint,
            } => {
                write!(
                    f,
                    "type mismatch: expected `{}`, got `{}`",
                    expected.display_truncated(&dc),
                    actual.display_truncated(&dc)
                )?;
                if let Some(hint) = hint {
                    write!(f, "\nhint: {hint}")?;
                }
                Ok(())
            }
            TixDiagnosticKind::MissingField {
                field,
                available_fields,
                suggestion,
            } => {
                write!(f, "missing field `{field}`")?;
                if let Some(suggestion) = suggestion {
                    write!(f, ", did you mean `{suggestion}`?")?;
                }
                if !available_fields.is_empty() {
                    write!(f, " (available fields: ")?;
                    for (i, name) in available_fields.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "`{name}`")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            TixDiagnosticKind::InvalidBinOp { op, lhs_ty, rhs_ty } => {
                write!(
                    f,
                    "cannot apply `{op}` to `{}` and `{}`",
                    lhs_ty.display_truncated(&dc),
                    rhs_ty.display_truncated(&dc)
                )
            }
            TixDiagnosticKind::InvalidAttrMerge { lhs_ty, rhs_ty } => {
                write!(
                    f,
                    "cannot merge `{}` with `{}`: both sides must be attribute sets",
                    lhs_ty.display_truncated(&dc),
                    rhs_ty.display_truncated(&dc)
                )
            }
            TixDiagnosticKind::UnresolvedName { name } => {
                write!(f, "unresolved name `{name}`")
            }
            TixDiagnosticKind::AnnotationArityMismatch {
                name,
                annotation_arity,
                expression_arity,
            } => {
                write!(
                    f,
                    "annotation for `{name}` has arity {annotation_arity} but expression has {expression_arity} parameters; skipping"
                )
            }
            TixDiagnosticKind::AnnotationUnchecked { name, reason } => {
                write!(
                    f,
                    "annotation for `{name}` accepted but not verified: {reason}"
                )
            }
            TixDiagnosticKind::AnnotationParseError { name, error } => {
                write!(f, "type annotation for `{name}` failed to parse: {error}")
            }
            TixDiagnosticKind::DuplicateKey { key, .. } => {
                write!(f, "duplicate key `{key}` in binding set")
            }
            TixDiagnosticKind::ImportNotFound { path } => {
                write!(f, "import target not found: {path}")
            }
            TixDiagnosticKind::AngleBracketImport { path } => {
                write!(
                    f,
                    "cannot resolve angle bracket import `{path}` — add a type annotation or stub"
                )
            }
            TixDiagnosticKind::ImportUnresolved { path } => {
                write!(
                    f,
                    "imported file `{path}` has not been analyzed — add it to [project] analyze in tix.toml or open it in the editor"
                )
            }
            TixDiagnosticKind::InvalidInterpolation { actual } => {
                write!(
                    f,
                    "`{}` cannot be used in string interpolation; \
                     use `toString` to convert it explicitly",
                    actual.display_truncated(&dc)
                )
            }
            TixDiagnosticKind::InferenceAborted { missing_bindings } => {
                if missing_bindings.is_empty() {
                    write!(
                        f,
                        "type inference aborted (memory limit exceeded) — partial results are available for bindings inferred before the limit was reached"
                    )
                } else if missing_bindings.len() <= 5 {
                    let names = missing_bindings
                        .iter()
                        .map(|n| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "type inference aborted (memory limit exceeded) — missing types for: {names}")
                } else {
                    let shown = missing_bindings[..5]
                        .iter()
                        .map(|n| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "type inference aborted (memory limit exceeded) — missing types for: {shown}, and {} more",
                        missing_bindings.len() - 5
                    )
                }
            }
        }
    }
}

impl fmt::Display for TixDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

// ==============================================================================
// Edit Distance (Levenshtein)
// ==============================================================================

/// Standard Levenshtein edit distance between two strings.
pub fn edit_distance(a: &str, b: &str) -> usize {
    let a_len = a.len();
    let b_len = b.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    // Use a single row for the DP table (space optimization).
    let mut prev_row: Vec<usize> = (0..=b_len).collect();
    let mut curr_row = vec![0; b_len + 1];

    for (i, a_char) in a.chars().enumerate() {
        curr_row[0] = i + 1;

        for (j, b_char) in b.chars().enumerate() {
            let cost = if a_char == b_char { 0 } else { 1 };
            curr_row[j + 1] = (prev_row[j] + cost)
                .min(prev_row[j + 1] + 1)
                .min(curr_row[j] + 1);
        }

        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[b_len]
}

/// Find the best match for `needle` among `candidates`, returning it only if
/// the edit distance is within a reasonable threshold. The threshold is roughly
/// half the length of the needle (rounded up), capped at 3, and requiring at
/// least distance 1 (no exact matches — those wouldn't be missing).
pub fn suggest_similar<'a>(
    needle: &str,
    candidates: impl IntoIterator<Item = &'a SmolStr>,
) -> Option<SmolStr> {
    let max_dist = needle.len().div_ceil(2).clamp(1, 3);

    let mut best: Option<(SmolStr, usize)> = None;

    for candidate in candidates {
        let dist = edit_distance(needle, candidate);
        if dist == 0 || dist > max_dist {
            continue;
        }
        if best.as_ref().is_none_or(|(_, best_dist)| dist < *best_dist) {
            best = Some((candidate.clone(), dist));
        }
    }

    best.map(|(name, _)| name)
}

// ==============================================================================
// InferenceError → TixDiagnostic conversion
// ==============================================================================

/// Canonicalize a `Ty<TyId>` into an arena-interned `TyRef`.
///
/// Compound types (Lambda, List, AttrSet, etc.) require their child `TyId`s to
/// be canonicalized via `canonicalize_standalone` and then interned so that the
/// resulting `TyRef` children are valid indices into the same arena.
///
/// Leaf types (Primitive, TyVar) are interned directly without recursion.
/// `Frozen` types are imported from their own arena into the local one.
fn canonicalize_ty_structural(
    ty: &lang_ty::Ty<TyId>,
    table: &TypeStorage,
    arena: &mut TypeArena,
) -> lang_ty::TyRef {
    // Inline helper: canonicalize a child TyId and intern the resulting OutputTy.
    // Defined as a macro rather than a closure to avoid borrow-checker complaints
    // about `arena` being captured by the closure while also needed in the match arms.
    //
    // TODO: once canonicalize_standalone is updated to accept a `&mut TypeArena`
    // and return `TyRef` directly, remove the `arena.intern(...)` wrapper here.
    macro_rules! child {
        ($ty_id:expr, $pol:expr) => {{
            let (src_arena, src_ty) = canonicalize_standalone(table, $ty_id, $pol);
            let mut cache = rustc_hash::FxHashMap::default();
            lang_ty::arena::import_from_arena(arena, &src_arena, src_ty, &mut cache)
        }};
    }

    match ty {
        lang_ty::Ty::Primitive(p) => arena.intern(OutputTy::Primitive(*p)),
        lang_ty::Ty::TyVar(x) => arena.intern(OutputTy::TyVar(*x)),
        lang_ty::Ty::List(elem) => {
            let c_elem = child!(*elem, Polarity::Positive);
            arena.intern(OutputTy::List(c_elem))
        }
        lang_ty::Ty::Lambda { param, body } => {
            let c_param = child!(*param, Polarity::Negative);
            let c_body = child!(*body, Polarity::Positive);
            arena.intern(OutputTy::Lambda {
                param: c_param,
                body: c_body,
            })
        }
        lang_ty::Ty::AttrSet(attr) => {
            // Canonicalize each field and the dynamic field type before interning
            // the attrset node, since intern() requires all children to already
            // be valid indices in this arena.
            let fields: std::collections::BTreeMap<_, _> = attr
                .fields
                .iter()
                .map(|(k, &v)| (k.clone(), child!(v, Polarity::Positive)))
                .collect();
            let dyn_ty = attr.dyn_ty.map(|d| child!(d, Polarity::Positive));
            arena.intern(OutputTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            }))
        }
        lang_ty::Ty::Neg(inner) => {
            let c_inner = child!(*inner, Polarity::Positive);
            arena.intern(OutputTy::Neg(c_inner))
        }
        lang_ty::Ty::Inter(a, b) => {
            let ca = child!(*a, Polarity::Positive);
            let cb = child!(*b, Polarity::Positive);
            arena.intern(OutputTy::Intersection(vec![ca, cb]))
        }
        lang_ty::Ty::Union(a, b) => {
            let ca = child!(*a, Polarity::Positive);
            let cb = child!(*b, Polarity::Positive);
            arena.intern(OutputTy::Union(vec![ca, cb]))
        }
        lang_ty::Ty::Named(name, inner) => {
            let c = child!(*inner, Polarity::Positive);
            arena.intern(OutputTy::Named(name.clone(), c))
        }
        // Frozen types carry their own arena; reference it zero-copy.
        lang_ty::Ty::Frozen(owned) => arena.intern(OutputTy::Extern(owned.clone())),
    }
}

/// Wrap a `TyRef` and the arena it lives in as a self-contained `DiagTy`.
fn make_diag_ty(arena: Arc<TypeArena>, ty: lang_ty::TyRef) -> DiagTy {
    DiagTy(OwnedTy::new(arena, ty))
}

/// Check whether a TypeMismatch deserves a contextual hint and, if so, return
/// one. Currently recognised cases:
///
/// 1. **expected=path, actual=string on a StringInterpolation** — suggest path
///    concatenation with `+`.
/// 2. **expected=string, actual=non-string** — suggest `toString` (and
///    `"${...}"` when the actual type supports Nix string interpolation).
fn type_mismatch_hint(
    arena: &TypeArena,
    expected: lang_ty::TyRef,
    actual: lang_ty::TyRef,
    at_expr: ExprId,
    module: &Module,
) -> Option<String> {
    use lang_ty::PrimitiveTy;

    // Case 1: string interpolation used where path is expected.
    let is_expected_path = matches!(arena.get(expected), OutputTy::Primitive(PrimitiveTy::Path));
    let is_actual_string = matches!(arena.get(actual), OutputTy::Primitive(PrimitiveTy::String));

    if is_expected_path
        && is_actual_string
        && matches!(&module[at_expr], Expr::StringInterpolation(_))
    {
        return Some(
            "string interpolation always produces `string`; \
             use `path + \"/suffix\"` to preserve the `path` type"
                .to_string(),
        );
    }

    // Case 2: non-string passed where string is expected (Nix coercion).
    let is_expected_string = matches!(
        arena.get(expected),
        OutputTy::Primitive(PrimitiveTy::String)
    );
    if is_expected_string && !is_actual_string {
        if supports_string_interpolation(arena, actual) {
            return Some(
                "Nix coerces this type to `string` implicitly; \
                 use `toString expr` or `\"${...}\"` to make the conversion explicit"
                    .to_string(),
            );
        } else {
            return Some(
                "Nix coerces this type to `string` implicitly; \
                 use `toString expr` to make the conversion explicit"
                    .to_string(),
            );
        }
    }

    None
}

/// Whether a type supports Nix's `"${expr}"` string interpolation.
///
/// In Nix, interpolation works for strings, paths, and derivations (attrsets
/// with `outPath`). It does NOT work for int, bool, float, null, lists, or
/// lambdas — those require an explicit `toString` call.
fn supports_string_interpolation(arena: &TypeArena, ty: lang_ty::TyRef) -> bool {
    match arena.get(ty) {
        OutputTy::Primitive(lang_ty::PrimitiveTy::String)
        | OutputTy::Primitive(lang_ty::PrimitiveTy::Path)
        | OutputTy::AttrSet(_) => true,
        OutputTy::Named(_, inner) => supports_string_interpolation(arena, *inner),
        OutputTy::Union(members) => members
            .iter()
            .all(|m| supports_string_interpolation(arena, *m)),
        _ => false,
    }
}

/// Convert a single `LocatedError` into a `TixDiagnostic`.
///
/// Each error gets its own arena so that diagnostics are fully self-contained
/// and can be stored, cloned, or compared without keeping the TypeStorage alive.
fn error_to_diagnostic(
    error: &LocatedError,
    table: &TypeStorage,
    module: &Module,
) -> TixDiagnostic {
    let kind = match &error.payload {
        InferenceError::TypeMismatch(pair) => {
            let mut arena = TypeArena::new();
            let actual = canonicalize_ty_structural(&pair.0, table, &mut arena);
            let expected = canonicalize_ty_structural(&pair.1, table, &mut arena);
            let arena = Arc::new(arena);

            // When expected=path and actual=string, check if the expression is
            // a StringInterpolation — suggest using path concatenation instead.
            let hint = type_mismatch_hint(&arena, expected, actual, error.at_expr, module);

            TixDiagnosticKind::TypeMismatch {
                expected: make_diag_ty(Arc::clone(&arena), expected),
                actual: make_diag_ty(Arc::clone(&arena), actual),
                hint,
            }
        }
        InferenceError::MissingField { field, available } => {
            let suggestion = suggest_similar(field, available.iter());
            TixDiagnosticKind::MissingField {
                field: field.clone(),
                available_fields: available.clone(),
                suggestion,
            }
        }
        InferenceError::InvalidBinOp(triple) => {
            let mut arena = TypeArena::new();
            let lhs_ty = canonicalize_ty_structural(&triple.1, table, &mut arena);
            let rhs_ty = canonicalize_ty_structural(&triple.2, table, &mut arena);
            let arena = Arc::new(arena);
            TixDiagnosticKind::InvalidBinOp {
                op: triple.0,
                lhs_ty: make_diag_ty(Arc::clone(&arena), lhs_ty),
                rhs_ty: make_diag_ty(Arc::clone(&arena), rhs_ty),
            }
        }
        InferenceError::InvalidAttrMerge(pair) => {
            let mut arena = TypeArena::new();
            let lhs_ty = canonicalize_ty_structural(&pair.0, table, &mut arena);
            let rhs_ty = canonicalize_ty_structural(&pair.1, table, &mut arena);
            let arena = Arc::new(arena);
            TixDiagnosticKind::InvalidAttrMerge {
                lhs_ty: make_diag_ty(Arc::clone(&arena), lhs_ty),
                rhs_ty: make_diag_ty(Arc::clone(&arena), rhs_ty),
            }
        }
    };

    TixDiagnostic {
        at_expr: error.at_expr,
        kind,
    }
}

/// Convert a `LocatedWarning` into a `TixDiagnostic`.
fn warning_to_diagnostic(warning: &LocatedWarning) -> TixDiagnostic {
    let kind = match &warning.payload {
        Warning::UnresolvedName(name) => TixDiagnosticKind::UnresolvedName { name: name.clone() },
        Warning::AnnotationArityMismatch {
            name,
            annotation_arity,
            expression_arity,
        } => TixDiagnosticKind::AnnotationArityMismatch {
            name: name.clone(),
            annotation_arity: *annotation_arity,
            expression_arity: *expression_arity,
        },
        Warning::AnnotationUnchecked { name, reason } => TixDiagnosticKind::AnnotationUnchecked {
            name: name.clone(),
            reason: reason.clone(),
        },
        Warning::AnnotationParseError { name, error } => TixDiagnosticKind::AnnotationParseError {
            name: name.clone(),
            error: error.clone(),
        },
    };

    TixDiagnostic {
        at_expr: warning.at_expr,
        kind,
    }
}

/// Convert a batch of `LocatedError`s into `TixDiagnostic`s.
pub fn errors_to_diagnostics(
    errors: &[LocatedError],
    table: &TypeStorage,
    module: &Module,
) -> Vec<TixDiagnostic> {
    errors
        .iter()
        .map(|e| error_to_diagnostic(e, table, module))
        .collect()
}

/// Convert a batch of `LocatedWarning`s into `TixDiagnostic`s.
pub fn warnings_to_diagnostics(warnings: &[Located<Warning>]) -> Vec<TixDiagnostic> {
    warnings.iter().map(warning_to_diagnostic).collect()
}

/// Convert lowering-phase diagnostics into `TixDiagnostic`s.
///
/// Lowering diagnostics carry their own `AstPtr` spans (they don't have an
/// `ExprId` location). We use `fallback_expr` (typically `module.entry_expr`)
/// for the `at_expr` field; the rendering code in CLI and LSP uses the
/// embedded spans directly for `DuplicateKey`.
pub fn lower_diagnostics_to_tix(
    lower_diags: &[lang_ast::LowerDiagnostic],
    fallback_expr: ExprId,
) -> Vec<TixDiagnostic> {
    lower_diags
        .iter()
        .map(|ld| match ld {
            lang_ast::LowerDiagnostic::DuplicateKey { key, first, second } => TixDiagnostic {
                at_expr: fallback_expr,
                kind: TixDiagnosticKind::DuplicateKey {
                    key: key.clone(),
                    first: *first,
                    second: *second,
                },
            },
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use lang_ty::{OwnedTy, TypeArena};

    use super::*;

    /// Construct a `DiagTy` for a primitive type, for use in test assertions.
    ///
    /// `DiagTy::PartialEq` compares by display string, so two `DiagTy` values
    /// wrapping the same primitive type will compare equal even if they live in
    /// different arenas.
    fn prim_owned(p: lang_ty::PrimitiveTy) -> DiagTy {
        let mut arena = TypeArena::new();
        let ty = arena.intern(OutputTy::Primitive(p));
        DiagTy(OwnedTy::new(Arc::new(arena), ty))
    }

    #[test]
    fn edit_distance_identical() {
        assert_eq!(edit_distance("foo", "foo"), 0);
    }

    #[test]
    fn edit_distance_single_substitution() {
        assert_eq!(edit_distance("foo", "fop"), 1);
    }

    #[test]
    fn edit_distance_transposition_is_two() {
        assert_eq!(edit_distance("bar", "bra"), 2);
    }

    #[test]
    fn edit_distance_empty() {
        assert_eq!(edit_distance("", "abc"), 3);
        assert_eq!(edit_distance("abc", ""), 3);
        assert_eq!(edit_distance("", ""), 0);
    }

    #[test]
    fn suggest_similar_finds_close_match() {
        let candidates: Vec<SmolStr> = vec!["foo".into(), "bar".into(), "baz".into()];
        assert_eq!(
            suggest_similar("bra", candidates.iter()),
            Some(SmolStr::from("bar"))
        );
    }

    #[test]
    fn suggest_similar_rejects_distant_names() {
        let candidates: Vec<SmolStr> = vec!["foo".into(), "bar".into()];
        assert_eq!(suggest_similar("xyz", candidates.iter()), None);
    }

    #[test]
    fn suggest_similar_rejects_exact_match() {
        let candidates: Vec<SmolStr> = vec!["foo".into()];
        assert_eq!(suggest_similar("foo", candidates.iter()), None);
    }

    #[test]
    fn suggest_similar_no_false_positive_for_very_different() {
        let candidates: Vec<SmolStr> = vec!["foo".into()];
        assert_eq!(
            suggest_similar("completely_different", candidates.iter()),
            None
        );
    }

    #[test]
    fn type_mismatch_display() {
        let kind = TixDiagnosticKind::TypeMismatch {
            expected: prim_owned(lang_ty::PrimitiveTy::String),
            actual: prim_owned(lang_ty::PrimitiveTy::Int),
            hint: None,
        };
        assert_eq!(
            kind.to_string(),
            "type mismatch: expected `string`, got `int`"
        );
    }

    #[test]
    fn missing_field_display_with_suggestion() {
        let kind = TixDiagnosticKind::MissingField {
            field: "bra".into(),
            available_fields: vec!["foo".into(), "bar".into(), "baz".into()],
            suggestion: Some("bar".into()),
        };
        let msg = kind.to_string();
        assert!(msg.contains("missing field `bra`"));
        assert!(msg.contains("did you mean `bar`?"));
        assert!(msg.contains("available fields:"));
    }

    #[test]
    fn missing_field_display_without_suggestion() {
        let kind = TixDiagnosticKind::MissingField {
            field: "xyz".into(),
            available_fields: vec!["foo".into(), "bar".into()],
            suggestion: None,
        };
        let msg = kind.to_string();
        assert!(msg.contains("missing field `xyz`"));
        assert!(!msg.contains("did you mean"));
    }

    #[test]
    fn invalid_bin_op_display() {
        let kind = TixDiagnosticKind::InvalidBinOp {
            op: OverloadBinOp::Sub,
            lhs_ty: prim_owned(lang_ty::PrimitiveTy::String),
            rhs_ty: prim_owned(lang_ty::PrimitiveTy::Int),
        };
        assert_eq!(kind.to_string(), "cannot apply `-` to `string` and `int`");
    }

    #[test]
    fn invalid_attr_merge_display() {
        let kind = TixDiagnosticKind::InvalidAttrMerge {
            lhs_ty: prim_owned(lang_ty::PrimitiveTy::Int),
            rhs_ty: prim_owned(lang_ty::PrimitiveTy::Int),
        };
        let msg = kind.to_string();
        assert!(msg.contains("cannot merge"));
        assert!(msg.contains("both sides must be attribute sets"));
    }

    #[test]
    fn unresolved_name_display() {
        let kind = TixDiagnosticKind::UnresolvedName { name: "foo".into() };
        assert_eq!(kind.to_string(), "unresolved name `foo`");
    }

    #[test]
    fn annotation_unchecked_display() {
        let kind = TixDiagnosticKind::AnnotationUnchecked {
            name: "dispatch".into(),
            reason: "intersection-of-function annotations are accepted as declared types but not verified against the body".into(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("dispatch"));
        assert!(msg.contains("not verified"));
    }

    #[test]
    fn import_not_found_display() {
        let kind = TixDiagnosticKind::ImportNotFound {
            path: "/tmp/missing.nix".to_string(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("import target not found"));
        assert!(msg.contains("/tmp/missing.nix"));
    }

    #[test]
    fn inference_aborted_display_no_missing() {
        let kind = TixDiagnosticKind::InferenceAborted {
            missing_bindings: vec![],
        };
        let msg = kind.to_string();
        assert!(msg.contains("aborted"));
        assert!(msg.contains("partial results"));
    }

    #[test]
    fn inference_aborted_display_with_missing() {
        let kind = TixDiagnosticKind::InferenceAborted {
            missing_bindings: vec!["x".into(), "y".into()],
        };
        let msg = kind.to_string();
        assert!(msg.contains("aborted"));
        assert!(msg.contains("`x`"));
        assert!(msg.contains("`y`"));
        assert!(!msg.contains("and"), "should not truncate for <=5 items");
    }

    #[test]
    fn inference_aborted_display_truncated() {
        let kind = TixDiagnosticKind::InferenceAborted {
            missing_bindings: vec![
                "a".into(),
                "b".into(),
                "c".into(),
                "d".into(),
                "e".into(),
                "f".into(),
                "g".into(),
            ],
        };
        let msg = kind.to_string();
        assert!(msg.contains("aborted"));
        assert!(msg.contains("`a`"));
        assert!(msg.contains("`e`"));
        assert!(msg.contains("and 2 more"));
    }

    // ==================================================================
    // Error codes
    // ==================================================================

    #[test]
    fn diagnostic_codes_are_stable() {
        assert_eq!(
            TixDiagnosticKind::TypeMismatch {
                expected: prim_owned(lang_ty::PrimitiveTy::Int),
                actual: prim_owned(lang_ty::PrimitiveTy::String),
                hint: None,
            }
            .code(),
            "E001"
        );
        assert_eq!(
            TixDiagnosticKind::InvalidBinOp {
                op: OverloadBinOp::Add,
                lhs_ty: prim_owned(lang_ty::PrimitiveTy::Int),
                rhs_ty: prim_owned(lang_ty::PrimitiveTy::String),
            }
            .code(),
            "E003"
        );
        assert_eq!(
            TixDiagnosticKind::AngleBracketImport {
                path: "<nixpkgs>".to_string(),
            }
            .code(),
            "E012"
        );
        assert_eq!(
            TixDiagnosticKind::ImportUnresolved {
                path: "/foo.nix".to_string(),
            }
            .code(),
            "E013"
        );
    }

    #[test]
    fn docs_url_format() {
        let kind = TixDiagnosticKind::TypeMismatch {
            expected: prim_owned(lang_ty::PrimitiveTy::Int),
            actual: prim_owned(lang_ty::PrimitiveTy::String),
            hint: None,
        };
        assert_eq!(
            kind.docs_url(),
            "https://jrmurr.github.io/tix/diagnostics/e001.html"
        );
    }

    #[test]
    fn is_warning_classification() {
        assert!(TixDiagnosticKind::UnresolvedName { name: "x".into() }.is_warning());
        assert!(TixDiagnosticKind::AngleBracketImport {
            path: "<nixpkgs>".to_string()
        }
        .is_warning());
        assert!(TixDiagnosticKind::ImportUnresolved {
            path: "/foo.nix".to_string()
        }
        .is_warning());
        assert!(!TixDiagnosticKind::TypeMismatch {
            expected: prim_owned(lang_ty::PrimitiveTy::Int),
            actual: prim_owned(lang_ty::PrimitiveTy::String),
            hint: None,
        }
        .is_warning());
    }

    // ==================================================================
    // New variant display
    // ==================================================================

    #[test]
    fn angle_bracket_import_display() {
        let kind = TixDiagnosticKind::AngleBracketImport {
            path: "<nixpkgs>".to_string(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("angle bracket import"));
        assert!(msg.contains("<nixpkgs>"));
        assert!(msg.contains("stub"));
    }

    #[test]
    fn import_unresolved_display() {
        let kind = TixDiagnosticKind::ImportUnresolved {
            path: "/tmp/lib.nix".to_string(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("/tmp/lib.nix"));
        assert!(msg.contains("not been analyzed"));
    }
}
