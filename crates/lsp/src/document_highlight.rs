// ==============================================================================
// textDocument/documentHighlight — highlight all occurrences of a name
// ==============================================================================
//
// Same-file variant of find-references, with Read/Write classification.
// The definition site gets WRITE, reference sites get READ.

use rowan::ast::AstNode;
use tower_lsp::lsp_types::{DocumentHighlight, DocumentHighlightKind, Position};

use crate::state::FileSnapshot;

pub fn document_highlight(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
) -> Vec<DocumentHighlight> {
    let target = match crate::references::name_at_position(analysis, pos, root) {
        Some(n) => n,
        None => return Vec::new(),
    };

    let mut highlights = Vec::new();

    // Definition site — WRITE.
    if let Some(ptr) = analysis.syntax.source_map.nodes_for_name(target).next() {
        let node = ptr.to_node(root.syntax());
        let range = analysis.syntax.line_index.range(node.text_range());
        highlights.push(DocumentHighlight {
            range,
            kind: Some(DocumentHighlightKind::WRITE),
        });
    }

    // Reference sites — READ.
    for &expr_id in analysis.syntax.name_res.refs_to(target) {
        if let Some(ptr) = analysis.syntax.source_map.node_for_expr(expr_id) {
            let node = ptr.to_node(root.syntax());
            let range = analysis.syntax.line_index.range(node.text_range());
            highlights.push(DocumentHighlight {
                range,
                kind: Some(DocumentHighlightKind::READ),
            });
        }
    }

    highlights
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;

    fn highlight_at_marker(src: &str, marker: u32) -> Vec<DocumentHighlight> {
        let markers = parse_markers(src);
        let offset = markers[&marker];
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();
        let pos = analysis.syntax.line_index.position(offset);
        document_highlight(&analysis, pos, &t.root)
    }

    fn count_kinds(highlights: &[DocumentHighlight]) -> (usize, usize) {
        let writes = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::WRITE))
            .count();
        let reads = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::READ))
            .count();
        (writes, reads)
    }

    #[test]
    fn highlights_let_binding() {
        let src = indoc! {"
            let x = 1; in x + x
            #   ^1
        "};

        let highlights = highlight_at_marker(src, 1);
        let (writes, reads) = count_kinds(&highlights);
        assert_eq!(writes, 1, "should have 1 write (definition)");
        assert_eq!(reads, 2, "should have 2 reads (references)");
    }

    #[test]
    fn cursor_on_literal_returns_empty() {
        let src = indoc! {"
            let x = 1; in x
            #       ^1
        "};

        let highlights = highlight_at_marker(src, 1);
        assert!(highlights.is_empty());
    }

    #[test]
    fn lambda_param_highlight() {
        let src = indoc! {"
            let f = x: x; in f
            #       ^1
        "};

        let highlights = highlight_at_marker(src, 1);
        let (writes, reads) = count_kinds(&highlights);
        assert_eq!(writes, 1, "param definition is a write");
        assert_eq!(reads, 1, "param usage in body is a read");
    }
}
