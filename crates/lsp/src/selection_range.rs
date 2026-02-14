// ==============================================================================
// textDocument/selectionRange — expanding selection via syntax tree
// ==============================================================================
//
// For each cursor position, walks up the rnix syntax tree from the token to
// the root, collecting progressively larger ranges. The editor uses this to
// implement "Expand Selection" (Ctrl+Shift+→ in VS Code).

use tower_lsp::lsp_types::{Position, SelectionRange};

use crate::state::FileAnalysis;

pub fn selection_ranges(
    analysis: &FileAnalysis,
    positions: Vec<Position>,
    root: &rnix::Root,
) -> Vec<SelectionRange> {
    positions
        .into_iter()
        .map(|pos| build_selection_range(analysis, pos, root))
        .collect()
}

fn build_selection_range(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
) -> SelectionRange {
    use rowan::ast::AstNode;

    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased();

    let token = match token {
        Some(t) => t,
        None => {
            return SelectionRange {
                range: tower_lsp::lsp_types::Range::new(pos, pos),
                parent: None,
            }
        }
    };

    // Collect all unique ranges from the token up through each ancestor node.
    let mut ranges = Vec::new();
    let token_range = analysis.line_index.range(token.text_range());
    ranges.push(token_range);

    let mut node = match token.parent() {
        Some(n) => n,
        None => {
            return SelectionRange {
                range: token_range,
                parent: None,
            }
        }
    };

    loop {
        let r = analysis.line_index.range(node.text_range());
        // Deduplicate: only add if different from the last range.
        if ranges.last() != Some(&r) {
            ranges.push(r);
        }
        match node.parent() {
            Some(parent) => node = parent,
            None => break,
        }
    }

    // Build the linked list from innermost (first) to outermost (last).
    // We iterate in reverse: start with the outermost as the base (no parent),
    // then wrap each subsequent inner range around it.
    let mut result = SelectionRange {
        range: *ranges.last().unwrap(),
        parent: None,
    };

    for &r in ranges.iter().rev().skip(1) {
        result = SelectionRange {
            range: r,
            parent: Some(Box::new(result)),
        };
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, temp_path};
    use lang_check::aliases::TypeAliasRegistry;

    fn get_ranges(src: &str, offset: u32) -> Vec<tower_lsp::lsp_types::Range> {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();
        let pos = analysis.line_index.position(offset);

        let results = selection_ranges(analysis, vec![pos], &root);
        assert_eq!(results.len(), 1);

        // Flatten the linked list into a Vec.
        let mut ranges = Vec::new();
        let mut current = Some(&results[0]);
        while let Some(sr) = current {
            ranges.push(sr.range);
            current = sr.parent.as_deref();
        }
        ranges
    }

    #[test]
    fn ranges_nest_from_token_to_root() {
        let src = "let x = 1; in x";
        let offset = find_offset(src, "1");
        let ranges = get_ranges(src, offset);

        // Should have at least: token "1" → literal → binding value → let-in → root
        assert!(
            ranges.len() >= 2,
            "should have nested ranges, got {ranges:?}"
        );

        // Innermost should be the token "1" range.
        let first = ranges[0];
        assert_eq!(first.start.character as u32, offset);
        assert_eq!(first.end.character as u32, offset + 1);

        // Outermost should cover the whole source.
        let last = ranges.last().unwrap();
        assert_eq!(last.start, Position::new(0, 0));
    }

    #[test]
    fn multiple_positions_in_one_request() {
        let src = "let x = 1; in x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let pos1 = analysis.line_index.position(find_offset(src, "1"));
        let pos2 = analysis.line_index.position(find_offset(src, "in x") + 3);

        let results = selection_ranges(analysis, vec![pos1, pos2], &root);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn deduplicates_identical_ranges() {
        let src = "let x = 1; in x";
        let offset = find_offset(src, "1");
        let ranges = get_ranges(src, offset);

        // No two consecutive ranges should be identical.
        for pair in ranges.windows(2) {
            assert_ne!(pair[0], pair[1], "consecutive ranges should differ");
        }
    }
}
