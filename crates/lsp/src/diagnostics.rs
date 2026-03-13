// ==============================================================================
// TixDiagnostic -> LSP Diagnostic conversion
// ==============================================================================

use std::collections::HashSet;

use lang_ast::{Module, ModuleSourceMap, NameId, NameKind};
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use lang_check::CheckResult;
use lang_ty::OutputTy;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{
    CodeDescription, Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location,
    NumberOrString, Range, Url,
};

use crate::config::DiagnosticLevel;
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

            let severity = if diag.kind.is_warning() {
                // ImportUnresolved is hint-level (normal for unconfigured projects).
                if matches!(diag.kind, TixDiagnosticKind::ImportUnresolved { .. }) {
                    DiagnosticSeverity::HINT
                } else {
                    DiagnosticSeverity::WARNING
                }
            } else {
                DiagnosticSeverity::ERROR
            };

            Diagnostic {
                range,
                severity: Some(severity),
                code: Some(NumberOrString::String(diag.kind.code().to_string())),
                code_description: Url::parse(&diag.kind.docs_url())
                    .ok()
                    .map(|href| CodeDescription { href }),
                source: Some("tix".to_string()),
                message: diag.kind.to_string(),
                related_information,
                ..Default::default()
            }
        })
        .collect()
}

// ==============================================================================
// Unknown-type (`?`) diagnostics
// ==============================================================================
//
// When a non-param binding has a bare type variable (unconstrained), it shows
// as `?` in hover/inlay hints. This function generates configurable diagnostics
// for those bindings so users know what to do about it.

/// Stable error code for unknown-type diagnostics (E014).
const UNKNOWN_TYPE_CODE: &str = "E014";
const UNKNOWN_TYPE_DOCS_URL: &str = "https://jrmurr.github.io/tix/diagnostics/e014.html";

/// Generate LSP diagnostics for bindings whose inferred type is `?` (bare type
/// variable). Skips params/pat-fields (genuinely polymorphic) and names that
/// already have a diagnostic from the core checker.
pub fn unknown_type_diagnostics(
    check_result: &CheckResult,
    module: &Module,
    source_map: &ModuleSourceMap,
    line_index: &LineIndex,
    root: &rnix::Root,
    level: DiagnosticLevel,
) -> Vec<Diagnostic> {
    let severity = match level.to_lsp_severity() {
        Some(s) => s,
        None => return vec![], // Off — skip entirely
    };

    let inference = match &check_result.inference {
        Some(inf) => inf,
        None => return vec![],
    };

    // Collect NameIds that already have a diagnostic to avoid double-reporting.
    // For example, UnresolvedName already explains why the type is unknown.
    let diagnosed_names: HashSet<NameId> =
        collect_diagnosed_names(&check_result.diagnostics, module, source_map);

    let mut diags = Vec::new();

    for (name_id, ty) in inference.name_ty_map.iter() {
        // Only bare type variables (unconstrained) — compound types like
        // `a -> a` are genuinely polymorphic, not unknown.
        if !matches!(ty, OutputTy::TyVar(_)) {
            continue;
        }

        let name = &module[name_id];

        // Params and pattern fields are genuinely polymorphic — `x: x` has
        // type `a -> a` where `x :: a`, and that's correct.
        if matches!(name.kind, NameKind::Param | NameKind::PatField) {
            continue;
        }

        // Skip names that already have a diagnostic.
        if diagnosed_names.contains(&name_id) {
            continue;
        }

        // Find the source range for this name.
        let range = source_map
            .nodes_for_name(name_id)
            .next()
            .map(|ptr| {
                let node = ptr.to_node(root.syntax());
                line_index.range(node.text_range())
            })
            .unwrap_or_else(|| Range::new(Default::default(), Default::default()));

        let message = format!(
            "type of `{}` could not be inferred — consider adding a type annotation or stub",
            name.text
        );

        diags.push(Diagnostic {
            range,
            severity: Some(severity),
            code: Some(NumberOrString::String(UNKNOWN_TYPE_CODE.to_string())),
            code_description: Url::parse(UNKNOWN_TYPE_DOCS_URL)
                .ok()
                .map(|href| CodeDescription { href }),
            source: Some("tix".to_string()),
            message,
            ..Default::default()
        });
    }

    diags
}

/// Collect NameIds that have an existing diagnostic targeting them.
/// Uses the source map to map ExprId → NameId where possible.
fn collect_diagnosed_names(
    diagnostics: &[TixDiagnostic],
    _module: &Module,
    source_map: &ModuleSourceMap,
) -> HashSet<NameId> {
    let mut names = HashSet::new();
    for diag in diagnostics {
        // Map the diagnostic's expression location to a NameId.
        // Unresolved names typically don't appear in name_ty_map anyway
        // (they're not successfully inferred), so this covers the main case
        // of import-related diagnostics that would overlap with unknown-type.
        if let Some(ptr) = source_map.node_for_expr(diag.at_expr) {
            if let Some(name_id) = source_map.name_for_node(ptr) {
                names.insert(name_id);
            }
        }
    }
    names
}
