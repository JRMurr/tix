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
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, temp_path};
    use lang_check::aliases::TypeAliasRegistry;

    #[test]
    fn rename_let_binding() {
        let src = "let foo = 1; in foo";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let uri = Url::from_file_path(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let def_offset = find_offset(src, "foo = 1");
        let pos = analysis.line_index.position(def_offset);

        let edit = rename(analysis, pos, "bar", &uri, &root);
        let edit = edit.expect("should produce a workspace edit");
        let file_edits = edit.changes.unwrap();
        let edits = &file_edits[&uri];
        assert_eq!(edits.len(), 2, "should rename definition + 1 reference");
        assert!(edits.iter().all(|e| e.new_text == "bar"));
    }

    #[test]
    fn prepare_rename_on_literal_returns_none() {
        let src = "let x = 1; in x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let offset = find_offset(src, "1");
        let pos = analysis.line_index.position(offset);

        assert!(prepare_rename(analysis, pos, &root).is_none());
    }

    #[test]
    fn rename_with_multiple_references() {
        let src = "let x = 1; y = x; in y + x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let uri = Url::from_file_path(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let def_offset = find_offset(src, "x = 1");
        let pos = analysis.line_index.position(def_offset);

        let edit = rename(analysis, pos, "z", &uri, &root).unwrap();
        let file_edits = edit.changes.unwrap();
        let edits = &file_edits[&uri];
        assert_eq!(edits.len(), 3, "should rename definition + 2 references");
    }

    #[test]
    fn rename_pattern_field() {
        let src = "{ x, ... }: x";
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let uri = Url::from_file_path(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let def_offset = find_offset(src, "x, ");
        let pos = analysis.line_index.position(def_offset);

        let edit = rename(analysis, pos, "y", &uri, &root).unwrap();
        let file_edits = edit.changes.unwrap();
        let edits = &file_edits[&uri];
        assert_eq!(edits.len(), 2, "should rename pattern field + body reference");
    }
}
