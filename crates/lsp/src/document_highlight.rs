// ==============================================================================
// textDocument/documentHighlight — highlight all occurrences of a name
// ==============================================================================
//
// Same-file variant of find-references, with Read/Write classification.
// The definition site gets WRITE, reference sites get READ.

use lang_ast::nameres::ResolveResult;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{DocumentHighlight, DocumentHighlightKind, Position};

use crate::state::FileAnalysis;

pub fn document_highlight(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
) -> Vec<DocumentHighlight> {
    let target = match crate::references::name_at_position(analysis, pos, root) {
        Some(n) => n,
        None => return Vec::new(),
    };

    let mut highlights = Vec::new();

    // Definition site — WRITE.
    if let Some(ptr) = analysis.source_map.nodes_for_name(target).next() {
        let node = ptr.to_node(root.syntax());
        let range = analysis.line_index.range(node.text_range());
        highlights.push(DocumentHighlight {
            range,
            kind: Some(DocumentHighlightKind::WRITE),
        });
    }

    // Reference sites — READ.
    for (expr_id, resolved) in analysis.name_res.iter() {
        if let ResolveResult::Definition(name_id) = resolved {
            if *name_id == target {
                if let Some(ptr) = analysis.source_map.node_for_expr(expr_id) {
                    let node = ptr.to_node(root.syntax());
                    let range = analysis.line_index.range(node.text_range());
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::READ),
                    });
                }
            }
        }
    }

    highlights
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, temp_path};
    use lang_check::aliases::TypeAliasRegistry;

    #[test]
    fn highlights_let_binding() {
        let src = "let x = 1; in x + x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let def_offset = find_offset(src, "x = 1");
        let pos = analysis.line_index.position(def_offset);

        let highlights = document_highlight(analysis, pos, &root);
        let writes: Vec<_> = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::WRITE))
            .collect();
        let reads: Vec<_> = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::READ))
            .collect();

        assert_eq!(writes.len(), 1, "should have 1 write (definition)");
        assert_eq!(reads.len(), 2, "should have 2 reads (references)");
    }

    #[test]
    fn cursor_on_literal_returns_empty() {
        let src = "let x = 1; in x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let offset = find_offset(src, "1");
        let pos = analysis.line_index.position(offset);

        let highlights = document_highlight(analysis, pos, &root);
        assert!(highlights.is_empty());
    }

    #[test]
    fn lambda_param_highlight() {
        let src = "let f = x: x; in f";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        // Cursor on the first `x` (parameter definition).
        let offset = find_offset(src, "x: x");
        let pos = analysis.line_index.position(offset);

        let highlights = document_highlight(analysis, pos, &root);
        let writes: Vec<_> = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::WRITE))
            .collect();
        let reads: Vec<_> = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::READ))
            .collect();

        assert_eq!(writes.len(), 1, "param definition is a write");
        assert_eq!(reads.len(), 1, "param usage in body is a read");
    }
}
