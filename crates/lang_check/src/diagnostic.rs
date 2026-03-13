// ==============================================================================
// Display-Ready Diagnostics
// ==============================================================================
//
// TixDiagnostic is the public-facing error type, using OutputTy (which has a
// human-readable Display impl) instead of internal Ty<TyId>. Conversion from
// the internal InferenceError happens at the boundary between inference and
// output, while we still have access to TypeStorage for canonicalization.

use std::fmt;

use lang_ast::{AstPtr, ExprId, OverloadBinOp};
use lang_ty::OutputTy;
use smol_str::SmolStr;

use crate::collect::canonicalize_standalone;
use crate::storage::TypeStorage;
use crate::{InferenceError, Located, LocatedError, LocatedWarning, Polarity, TyId, Warning};

/// A display-ready diagnostic paired with the expression where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TixDiagnostic {
    pub at_expr: ExprId,
    pub kind: TixDiagnosticKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TixDiagnosticKind {
    TypeMismatch {
        expected: OutputTy,
        actual: OutputTy,
    },
    MissingField {
        field: SmolStr,
        available_fields: Vec<SmolStr>,
        suggestion: Option<SmolStr>,
    },
    InvalidBinOp {
        op: OverloadBinOp,
        lhs_ty: OutputTy,
        rhs_ty: OutputTy,
    },
    InvalidAttrMerge {
        lhs_ty: OutputTy,
        rhs_ty: OutputTy,
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
    /// Inference was aborted because the deadline was exceeded.
    /// Bindings inferred before the timeout still have types; only
    /// the remaining ones are missing.
    InferenceTimeout {
        /// Names of bindings that were not inferred before the deadline.
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
}

// ==============================================================================
// Diagnostic Error Codes
// ==============================================================================
//
// Every diagnostic has a stable error code (E001–E014) that appears in CLI
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
            TixDiagnosticKind::InferenceTimeout { .. } => "E008",
            TixDiagnosticKind::AnnotationArityMismatch { .. } => "E009",
            TixDiagnosticKind::AnnotationUnchecked { .. } => "E010",
            TixDiagnosticKind::AnnotationParseError { .. } => "E011",
            TixDiagnosticKind::AngleBracketImport { .. } => "E012",
            TixDiagnosticKind::ImportUnresolved { .. } => "E013",
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
                | TixDiagnosticKind::InferenceTimeout { .. }
                | TixDiagnosticKind::AngleBracketImport { .. }
                | TixDiagnosticKind::ImportUnresolved { .. }
        )
    }
}

impl fmt::Display for TixDiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TixDiagnosticKind::TypeMismatch { expected, actual } => {
                write!(f, "type mismatch: expected `{expected}`, got `{actual}`")
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
                write!(f, "cannot apply `{op}` to `{lhs_ty}` and `{rhs_ty}`")
            }
            TixDiagnosticKind::InvalidAttrMerge { lhs_ty, rhs_ty } => {
                write!(
                    f,
                    "cannot merge `{lhs_ty}` with `{rhs_ty}`: both sides must be attribute sets"
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
            TixDiagnosticKind::InferenceTimeout { missing_bindings } => {
                if missing_bindings.is_empty() {
                    write!(
                        f,
                        "type inference timed out — partial results are available for bindings inferred before the deadline"
                    )
                } else if missing_bindings.len() <= 5 {
                    let names = missing_bindings
                        .iter()
                        .map(|n| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "type inference timed out — missing types for: {names}")
                } else {
                    let shown = missing_bindings[..5]
                        .iter()
                        .map(|n| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "type inference timed out — missing types for: {shown}, and {} more",
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

/// Canonicalize a `Ty<TyId>` into an `OutputTy` for display purposes.
/// Uses positive polarity (output position) since error messages show types
/// as "what was produced" rather than "what was expected as input".
fn canonicalize_error_ty(ty: &lang_ty::Ty<TyId>, table: &TypeStorage) -> OutputTy {
    // If the Ty is concrete, we need to find its TyId in the table to
    // canonicalize it. For simple cases (primitives), we can convert directly.
    match ty {
        lang_ty::Ty::Primitive(p) => OutputTy::Primitive(*p),
        _ => {
            // For structural types, allocate into a temporary storage isn't
            // practical. Instead, recursively convert children.
            canonicalize_ty_structural(ty, table)
        }
    }
}

/// Recursively convert a Ty<TyId> to OutputTy by canonicalizing children.
fn canonicalize_ty_structural(ty: &lang_ty::Ty<TyId>, table: &TypeStorage) -> OutputTy {
    match ty {
        lang_ty::Ty::Primitive(p) => OutputTy::Primitive(*p),
        lang_ty::Ty::TyVar(x) => OutputTy::TyVar(*x),
        lang_ty::Ty::List(elem) => {
            let c_elem = canonicalize_standalone(table, *elem, Polarity::Positive);
            OutputTy::List(lang_ty::TyRef::from(c_elem))
        }
        lang_ty::Ty::Lambda { param, body } => {
            let c_param = canonicalize_standalone(table, *param, Polarity::Negative);
            let c_body = canonicalize_standalone(table, *body, Polarity::Positive);
            OutputTy::Lambda {
                param: lang_ty::TyRef::from(c_param),
                body: lang_ty::TyRef::from(c_body),
            }
        }
        lang_ty::Ty::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(k, &v)| {
                    let c_field = canonicalize_standalone(table, v, Polarity::Positive);
                    (k.clone(), lang_ty::TyRef::from(c_field))
                })
                .collect();
            let dyn_ty = attr.dyn_ty.map(|d| {
                lang_ty::TyRef::from(canonicalize_standalone(table, d, Polarity::Positive))
            });
            OutputTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }
        lang_ty::Ty::Neg(inner) => {
            let c_inner = canonicalize_standalone(table, *inner, Polarity::Positive);
            OutputTy::Neg(lang_ty::TyRef::from(c_inner))
        }
        lang_ty::Ty::Inter(a, b) => {
            let ca = canonicalize_standalone(table, *a, Polarity::Positive);
            let cb = canonicalize_standalone(table, *b, Polarity::Positive);
            OutputTy::Intersection(vec![lang_ty::TyRef::from(ca), lang_ty::TyRef::from(cb)])
        }
        lang_ty::Ty::Union(a, b) => {
            let ca = canonicalize_standalone(table, *a, Polarity::Positive);
            let cb = canonicalize_standalone(table, *b, Polarity::Positive);
            OutputTy::Union(vec![lang_ty::TyRef::from(ca), lang_ty::TyRef::from(cb)])
        }
        lang_ty::Ty::Named(name, inner) => {
            let c = canonicalize_standalone(table, *inner, Polarity::Positive);
            OutputTy::Named(name.clone(), lang_ty::TyRef::from(c))
        }
    }
}

/// Convert a single `LocatedError` into a `TixDiagnostic`.
fn error_to_diagnostic(error: &LocatedError, table: &TypeStorage) -> TixDiagnostic {
    let kind = match &error.payload {
        InferenceError::TypeMismatch(pair) => {
            let actual = canonicalize_error_ty(&pair.0, table);
            let expected = canonicalize_error_ty(&pair.1, table);
            TixDiagnosticKind::TypeMismatch { expected, actual }
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
            let lhs_ty = canonicalize_error_ty(&triple.1, table);
            let rhs_ty = canonicalize_error_ty(&triple.2, table);
            TixDiagnosticKind::InvalidBinOp {
                op: triple.0,
                lhs_ty,
                rhs_ty,
            }
        }
        InferenceError::InvalidAttrMerge(pair) => {
            let lhs_ty = canonicalize_error_ty(&pair.0, table);
            let rhs_ty = canonicalize_error_ty(&pair.1, table);
            TixDiagnosticKind::InvalidAttrMerge { lhs_ty, rhs_ty }
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
pub fn errors_to_diagnostics(errors: &[LocatedError], table: &TypeStorage) -> Vec<TixDiagnostic> {
    errors
        .iter()
        .map(|e| error_to_diagnostic(e, table))
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
    use super::*;

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
            expected: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
            actual: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
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
            lhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
            rhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
        };
        assert_eq!(kind.to_string(), "cannot apply `-` to `string` and `int`");
    }

    #[test]
    fn invalid_attr_merge_display() {
        let kind = TixDiagnosticKind::InvalidAttrMerge {
            lhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
            rhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
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
    fn inference_timeout_display_no_missing() {
        let kind = TixDiagnosticKind::InferenceTimeout {
            missing_bindings: vec![],
        };
        let msg = kind.to_string();
        assert!(msg.contains("timed out"));
        assert!(msg.contains("partial results"));
    }

    #[test]
    fn inference_timeout_display_with_missing() {
        let kind = TixDiagnosticKind::InferenceTimeout {
            missing_bindings: vec!["x".into(), "y".into()],
        };
        let msg = kind.to_string();
        assert!(msg.contains("timed out"));
        assert!(msg.contains("`x`"));
        assert!(msg.contains("`y`"));
        assert!(!msg.contains("and"), "should not truncate for <=5 items");
    }

    #[test]
    fn inference_timeout_display_truncated() {
        let kind = TixDiagnosticKind::InferenceTimeout {
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
        assert!(msg.contains("timed out"));
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
                expected: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
                actual: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
            }
            .code(),
            "E001"
        );
        assert_eq!(
            TixDiagnosticKind::InvalidBinOp {
                op: OverloadBinOp::Add,
                lhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
                rhs_ty: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
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
            expected: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
            actual: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
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
            expected: OutputTy::Primitive(lang_ty::PrimitiveTy::Int),
            actual: OutputTy::Primitive(lang_ty::PrimitiveTy::String),
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
