// ==============================================================================
// textDocument/rename + textDocument/prepareRename
// ==============================================================================
//
// Renames a name across all its definition and reference sites within a single
// file. Cross-file rename is not yet supported.

use lang_ast::nameres::ResolveResult;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::*;

use crate::state::FileAnalysis;

/// Verify that the cursor is on a renameable name and return its range.
pub fn prepare_rename(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
) -> Option<PrepareRenameResponse> {
    let target = crate::references::name_at_position(analysis, pos, root)?;

    // Get the name's source range.
    let ptr = analysis.source_map.nodes_for_name(target).next()?;
    let node = ptr.to_node(root.syntax());
    let range = analysis.line_index.range(node.text_range());
    let name_text = analysis.module[target].text.to_string();

    Some(PrepareRenameResponse::RangeWithPlaceholder {
        range,
        placeholder: name_text,
    })
}

/// Rename a name at the given position to `new_name`, producing a workspace edit.
pub fn rename(
    analysis: &FileAnalysis,
    pos: Position,
    new_name: &str,
    uri: &Url,
    root: &rnix::Root,
) -> Option<WorkspaceEdit> {
    let target = crate::references::name_at_position(analysis, pos, root)?;

    let mut edits = Vec::new();

    // Definition site.
    if let Some(ptr) = analysis.source_map.nodes_for_name(target).next() {
        let node = ptr.to_node(root.syntax());
        let range = analysis.line_index.range(node.text_range());
        edits.push(TextEdit {
            range,
            new_text: new_name.to_string(),
        });
    }

    // Reference sites.
    for (expr_id, resolved) in analysis.name_res.iter() {
        if let ResolveResult::Definition(name_id) = resolved {
            if *name_id == target {
                if let Some(ptr) = analysis.source_map.node_for_expr(expr_id) {
                    let node = ptr.to_node(root.syntax());
                    let range = analysis.line_index.range(node.text_range());
                    edits.push(TextEdit {
                        range,
                        new_text: new_name.to_string(),
                    });
                }
            }
        }
    }

    if edits.is_empty() {
        return None;
    }

    // TODO: cross-file rename (e.g. renaming an exported name should update importers).
    let mut changes = std::collections::HashMap::new();
    changes.insert(uri.clone(), edits);

    Some(WorkspaceEdit {
        changes: Some(changes),
        ..Default::default()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;

    fn rename_at_marker(src: &str, marker: u32, new_name: &str) -> Option<WorkspaceEdit> {
        let markers = parse_markers(src);
        let offset = markers[&marker];
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();
        let uri = t.uri();
        let pos = analysis.line_index.position(offset);
        rename(analysis, pos, new_name, &uri, &t.root)
    }

    fn edit_count(edit: &WorkspaceEdit) -> usize {
        edit.changes
            .as_ref()
            .map(|c| c.values().map(|v| v.len()).sum())
            .unwrap_or(0)
    }

    #[test]
    fn rename_let_binding() {
        let src = indoc! {"
            let foo = 1; in foo
            #   ^1
        "};

        let edit = rename_at_marker(src, 1, "bar").expect("should produce edit");
        assert_eq!(
            edit_count(&edit),
            2,
            "should rename definition + 1 reference"
        );
        let all_bar = edit
            .changes
            .unwrap()
            .values()
            .all(|edits| edits.iter().all(|e| e.new_text == "bar"));
        assert!(all_bar);
    }

    #[test]
    fn prepare_rename_on_literal_returns_none() {
        let src = indoc! {"
            let x = 1; in x
            #       ^1
        "};

        let markers = parse_markers(src);
        let offset = markers[&1];
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();
        let pos = analysis.line_index.position(offset);

        assert!(prepare_rename(analysis, pos, &t.root).is_none());
    }

    #[test]
    fn rename_with_multiple_references() {
        let src = indoc! {"
            let x = 1; y = x; in y + x
            #   ^1
        "};

        let edit = rename_at_marker(src, 1, "z").unwrap();
        assert_eq!(
            edit_count(&edit),
            3,
            "should rename definition + 2 references"
        );
    }

    #[test]
    fn rename_pattern_field() {
        let src = indoc! {"
            { x, ... }: x
            # ^1
        "};

        let edit = rename_at_marker(src, 1, "y").unwrap();
        assert_eq!(
            edit_count(&edit),
            2,
            "should rename pattern field + body reference"
        );
    }
}
