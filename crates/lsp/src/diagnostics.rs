// ==============================================================================
// TixDiagnostic -> LSP Diagnostic conversion
// ==============================================================================

use lang_ast::ModuleSourceMap;
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, Range, Url,
};

use crate::convert::LineIndex;

/// Convert collected TixDiagnostics into LSP diagnostics.
/// Each diagnostic is mapped to the source range of its associated expression,
/// falling back to the file start if the expression has no source location.
pub fn to_lsp_diagnostics(
    diagnostics: &[TixDiagnostic],
    source_map: &ModuleSourceMap,
    line_index: &LineIndex,
    root: &rnix::Root,
    uri: &Url,
) -> Vec<Diagnostic> {
    diagnostics
        .iter()
        .map(|diag| {
            // File-level diagnostics (like InferenceTimeout) should only
            // highlight the first line, not the entire file.
            let (range, related_information) =
                if matches!(diag.kind, TixDiagnosticKind::InferenceTimeout { .. }) {
                    (Range::new(Default::default(), Default::default()), None)
                } else if let TixDiagnosticKind::DuplicateKey { first, second, .. } = &diag.kind {
                    // DuplicateKey carries its own AstPtr spans; point the diagnostic
                    // at the duplicate (second) definition for maximum visibility.
                    let second_node = second.to_node(root.syntax());
                    let range = line_index.range(second_node.text_range());

                    // Add related_information pointing to the first definition so
                    // users can navigate to it directly from the diagnostic.
                    let first_node = first.to_node(root.syntax());
                    let first_range = line_index.range(first_node.text_range());
                    let related = DiagnosticRelatedInformation {
                        location: Location {
                            uri: uri.clone(),
                            range: first_range,
                        },
                        message: "first defined here".to_string(),
                    };
                    (range, Some(vec![related]))
                } else {
                    let range = source_map
                        .node_for_expr(diag.at_expr)
                        .map(|ptr| {
                            let node = ptr.to_node(root.syntax());
                            line_index.range(node.text_range())
                        })
                        .unwrap_or_else(|| Range::new(Default::default(), Default::default()));
                    (range, None)
                };

            let severity = match &diag.kind {
                TixDiagnosticKind::UnresolvedName { .. }
                | TixDiagnosticKind::AnnotationArityMismatch { .. }
                | TixDiagnosticKind::AnnotationUnchecked { .. }
                | TixDiagnosticKind::AnnotationParseError { .. }
                | TixDiagnosticKind::DuplicateKey { .. }
                | TixDiagnosticKind::ImportNotFound { .. }
                | TixDiagnosticKind::ImportCyclic { .. }
                | TixDiagnosticKind::ImportInferenceError { .. }
                | TixDiagnosticKind::InferenceTimeout { .. } => DiagnosticSeverity::WARNING,
                _ => DiagnosticSeverity::ERROR,
            };

            Diagnostic {
                range,
                severity: Some(severity),
                source: Some("tix".to_string()),
                message: diag.kind.to_string(),
                related_information,
                ..Default::default()
            }
        })
        .collect()
}
