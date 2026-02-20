// ==============================================================================
// TixDiagnostic -> LSP Diagnostic conversion
// ==============================================================================

use lang_ast::ModuleSourceMap;
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range};

use crate::convert::LineIndex;

/// Convert collected TixDiagnostics into LSP diagnostics.
/// Each diagnostic is mapped to the source range of its associated expression,
/// falling back to the file start if the expression has no source location.
pub fn to_lsp_diagnostics(
    diagnostics: &[TixDiagnostic],
    source_map: &ModuleSourceMap,
    line_index: &LineIndex,
    root: &rnix::Root,
) -> Vec<Diagnostic> {
    diagnostics
        .iter()
        .map(|diag| {
            let range = source_map
                .node_for_expr(diag.at_expr)
                .map(|ptr| {
                    let node = ptr.to_node(root.syntax());
                    line_index.range(node.text_range())
                })
                .unwrap_or_else(|| Range::new(Default::default(), Default::default()));

            let severity = match &diag.kind {
                TixDiagnosticKind::UnresolvedName { .. }
                | TixDiagnosticKind::AnnotationArityMismatch { .. }
                | TixDiagnosticKind::AnnotationUnchecked { .. } => DiagnosticSeverity::WARNING,
                _ => DiagnosticSeverity::ERROR,
            };

            Diagnostic {
                range,
                severity: Some(severity),
                source: Some("tix".to_string()),
                message: diag.kind.to_string(),
                ..Default::default()
            }
        })
        .collect()
}
