// ==============================================================================
// Display-Ready Diagnostics
// ==============================================================================
//
// TixDiagnostic is the public-facing error type, using OutputTy (which has a
// human-readable Display impl) instead of internal Ty<TyId>. Conversion from
// the internal InferenceError happens at the boundary between inference and
// output, while we still have access to TypeStorage for canonicalization.

use std::collections::HashMap;
use std::fmt;

use lang_ast::{ExprId, OverloadBinOp};
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
    /// An imported file could not be found on disk.
    ImportNotFound {
        path: String,
    },
    /// An import created a dependency cycle (A imports B imports A).
    ImportCyclic {
        path: String,
    },
    /// Type inference in an imported file produced errors.
    ImportInferenceError {
        path: String,
        message: String,
    },
    /// Inference was aborted because the deadline was exceeded.
    /// Bindings inferred before the timeout still have types; only
    /// the remaining ones are missing.
    InferenceTimeout,
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
            TixDiagnosticKind::ImportNotFound { path } => {
                write!(f, "import target not found: {path}")
            }
            TixDiagnosticKind::ImportCyclic { path } => {
                write!(f, "cyclic import detected: {path}")
            }
            TixDiagnosticKind::ImportInferenceError { path, message } => {
                write!(f, "error in imported file {path}: {message}")
            }
            TixDiagnosticKind::InferenceTimeout => {
                write!(
                    f,
                    "type inference timed out — partial results are available for bindings inferred before the deadline"
                )
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
fn canonicalize_error_ty(
    ty: &lang_ty::Ty<TyId>,
    table: &TypeStorage,
    provenance: &HashMap<TyId, SmolStr>,
) -> OutputTy {
    // If the Ty is concrete, we need to find its TyId in the table to
    // canonicalize it. For simple cases (primitives), we can convert directly.
    match ty {
        lang_ty::Ty::Primitive(p) => OutputTy::Primitive(*p),
        _ => {
            // For structural types, allocate into a temporary storage isn't
            // practical. Instead, recursively convert children.
            canonicalize_ty_structural(ty, table, provenance)
        }
    }
}

/// Recursively convert a Ty<TyId> to OutputTy by canonicalizing children.
fn canonicalize_ty_structural(
    ty: &lang_ty::Ty<TyId>,
    table: &TypeStorage,
    provenance: &HashMap<TyId, SmolStr>,
) -> OutputTy {
    match ty {
        lang_ty::Ty::Primitive(p) => OutputTy::Primitive(*p),
        lang_ty::Ty::TyVar(x) => OutputTy::TyVar(*x),
        lang_ty::Ty::List(elem) => {
            let c_elem = canonicalize_standalone(table, provenance, *elem, Polarity::Positive);
            OutputTy::List(lang_ty::TyRef::from(c_elem))
        }
        lang_ty::Ty::Lambda { param, body } => {
            let c_param = canonicalize_standalone(table, provenance, *param, Polarity::Negative);
            let c_body = canonicalize_standalone(table, provenance, *body, Polarity::Positive);
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
                    let c_field = canonicalize_standalone(table, provenance, v, Polarity::Positive);
                    (k.clone(), lang_ty::TyRef::from(c_field))
                })
                .collect();
            let dyn_ty = attr.dyn_ty.map(|d| {
                lang_ty::TyRef::from(canonicalize_standalone(
                    table,
                    provenance,
                    d,
                    Polarity::Positive,
                ))
            });
            OutputTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }
        lang_ty::Ty::Neg(inner) => {
            let c_inner = canonicalize_standalone(table, provenance, *inner, Polarity::Positive);
            OutputTy::Neg(lang_ty::TyRef::from(c_inner))
        }
        lang_ty::Ty::Inter(a, b) => {
            let ca = canonicalize_standalone(table, provenance, *a, Polarity::Positive);
            let cb = canonicalize_standalone(table, provenance, *b, Polarity::Positive);
            OutputTy::Intersection(vec![lang_ty::TyRef::from(ca), lang_ty::TyRef::from(cb)])
        }
        lang_ty::Ty::Union(a, b) => {
            let ca = canonicalize_standalone(table, provenance, *a, Polarity::Positive);
            let cb = canonicalize_standalone(table, provenance, *b, Polarity::Positive);
            OutputTy::Union(vec![lang_ty::TyRef::from(ca), lang_ty::TyRef::from(cb)])
        }
    }
}

/// Convert a single `LocatedError` into a `TixDiagnostic`.
fn error_to_diagnostic(
    error: &LocatedError,
    table: &TypeStorage,
    provenance: &HashMap<TyId, SmolStr>,
) -> TixDiagnostic {
    let kind = match &error.payload {
        InferenceError::TypeMismatch(pair) => {
            let actual = canonicalize_error_ty(&pair.0, table, provenance);
            let expected = canonicalize_error_ty(&pair.1, table, provenance);
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
            let lhs_ty = canonicalize_error_ty(&triple.1, table, provenance);
            let rhs_ty = canonicalize_error_ty(&triple.2, table, provenance);
            TixDiagnosticKind::InvalidBinOp {
                op: triple.0,
                lhs_ty,
                rhs_ty,
            }
        }
        InferenceError::InvalidAttrMerge(pair) => {
            let lhs_ty = canonicalize_error_ty(&pair.0, table, provenance);
            let rhs_ty = canonicalize_error_ty(&pair.1, table, provenance);
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
    provenance: &HashMap<TyId, SmolStr>,
) -> Vec<TixDiagnostic> {
    errors
        .iter()
        .map(|e| error_to_diagnostic(e, table, provenance))
        .collect()
}

/// Convert a batch of `LocatedWarning`s into `TixDiagnostic`s.
pub fn warnings_to_diagnostics(warnings: &[Located<Warning>]) -> Vec<TixDiagnostic> {
    warnings.iter().map(warning_to_diagnostic).collect()
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
    fn import_cyclic_display() {
        let kind = TixDiagnosticKind::ImportCyclic {
            path: "/tmp/cycle.nix".to_string(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("cyclic import"));
        assert!(msg.contains("/tmp/cycle.nix"));
    }

    #[test]
    fn import_inference_error_display() {
        let kind = TixDiagnosticKind::ImportInferenceError {
            path: "/tmp/bad.nix".to_string(),
            message: "type mismatch".to_string(),
        };
        let msg = kind.to_string();
        assert!(msg.contains("error in imported file"));
        assert!(msg.contains("/tmp/bad.nix"));
        assert!(msg.contains("type mismatch"));
    }

    #[test]
    fn inference_timeout_display() {
        let kind = TixDiagnosticKind::InferenceTimeout;
        let msg = kind.to_string();
        assert!(msg.contains("timed out"));
        assert!(msg.contains("partial results"));
    }
}
