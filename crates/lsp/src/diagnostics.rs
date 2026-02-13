// ==============================================================================
// InferenceError -> LSP Diagnostic conversion
// ==============================================================================

use lang_ast::ModuleSourceMap;
use lang_check::{LocatedError, LocatedWarning};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range};

use crate::convert::LineIndex;

/// Convert collected inference errors into LSP diagnostics.
/// Each error is mapped to the source range of its associated expression,
/// falling back to the file start if the expression has no source location.
pub fn to_diagnostics(
    errors: &[LocatedError],
    source_map: &ModuleSourceMap,
    line_index: &LineIndex,
    root: &rnix::Root,
) -> Vec<Diagnostic> {
    errors
        .iter()
        .map(|located| {
            let range = source_map
                .node_for_expr(located.at_expr)
                .map(|ptr| {
                    let node = ptr.to_node(root.syntax());
                    line_index.range(node.text_range())
                })
                .unwrap_or_else(|| Range::new(Default::default(), Default::default()));

            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("tix".to_string()),
                message: located.error.to_string(),
                ..Default::default()
            }
        })
        .collect()
}

/// Convert collected inference warnings into LSP diagnostics.
pub fn warnings_to_diagnostics(
    warnings: &[LocatedWarning],
    source_map: &ModuleSourceMap,
    line_index: &LineIndex,
    root: &rnix::Root,
) -> Vec<Diagnostic> {
    warnings
        .iter()
        .map(|located| {
            let range = source_map
                .node_for_expr(located.at_expr)
                .map(|ptr| {
                    let node = ptr.to_node(root.syntax());
                    line_index.range(node.text_range())
                })
                .unwrap_or_else(|| Range::new(Default::default(), Default::default()));

            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::WARNING),
                source: Some("tix".to_string()),
                message: located.warning.to_string(),
                ..Default::default()
            }
        })
        .collect()
}
