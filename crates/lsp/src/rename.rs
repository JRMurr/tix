// ==============================================================================
// textDocument/rename + textDocument/prepareRename
// ==============================================================================
//
// Renames a name across all its definition and reference sites within a single
// file. When the renamed binding is a top-level export (attrset field) and
// other open files import the current file, cross-file rename produces edits
// for `x.oldName` -> `x.newName` select expressions in those files. If
// importers exist but aren't open (so we can't update them), we attach a
// warning annotation to the workspace edit.

use std::collections::HashMap;
use std::path::PathBuf;

use lang_ast::{Expr, ExprId, Literal, NameId};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::*;

use crate::state::{AnalysisState, FileSnapshot};

/// Verify that the cursor is on a renameable name and return its range.
pub fn prepare_rename(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
) -> Option<PrepareRenameResponse> {
    let target = crate::references::name_at_position(analysis, pos, root)?;

    // Get the name's source range.
    let ptr = analysis.syntax.source_map.nodes_for_name(target).next()?;
    let node = ptr.to_node(root.syntax());
    let range = analysis.syntax.line_index.range(node.text_range());
    let name_text = analysis.syntax.module[target].text.to_string();

    Some(PrepareRenameResponse::RangeWithPlaceholder {
        range,
        placeholder: name_text,
    })
}

/// Result of a rename operation, including cross-file information.
pub struct RenameResult {
    pub edit: WorkspaceEdit,
    /// Warning message if importers exist that we couldn't fully update.
    pub warning: Option<String>,
}

/// Rename a name at the given position to `new_name`, producing a workspace edit.
///
/// When `state` and `current_path` are provided, also scans other open files
/// for import-site references (Select expressions like `lib.oldName`) and
/// includes cross-file edits. If some importers aren't open, a warning is
/// returned so the LSP can show it to the user.
pub fn rename(
    analysis: &FileSnapshot,
    pos: Position,
    new_name: &str,
    uri: &Url,
    root: &rnix::Root,
    state: Option<&AnalysisState>,
    current_path: Option<&PathBuf>,
) -> Option<RenameResult> {
    let target = crate::references::name_at_position(analysis, pos, root)?;

    let mut edits = Vec::new();

    // Definition site.
    if let Some(ptr) = analysis.syntax.source_map.nodes_for_name(target).next() {
        let node = ptr.to_node(root.syntax());
        let range = analysis.syntax.line_index.range(node.text_range());
        edits.push(TextEdit {
            range,
            new_text: new_name.to_string(),
        });
    }

    // Reference sites.
    for &expr_id in analysis.syntax.name_res.refs_to(target) {
        if let Some(ptr) = analysis.syntax.source_map.node_for_expr(expr_id) {
            let node = ptr.to_node(root.syntax());
            let range = analysis.syntax.line_index.range(node.text_range());
            edits.push(TextEdit {
                range,
                new_text: new_name.to_string(),
            });
        }
    }

    if edits.is_empty() {
        return None;
    }

    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    changes.insert(uri.clone(), edits);

    // ==============================================================================
    // Cross-file rename: update Select expressions in importing files
    // ==============================================================================
    //
    // If this binding is a top-level export (a field in the file's root attrset)
    // and other open files import this file, we can update `importer.oldName`
    // references in those files. We also warn when importers exist but aren't
    // open for editing.

    let old_name = analysis.syntax.module[target].text.as_str();
    let warning = if let (Some(state), Some(current_path)) = (state, current_path) {
        let is_top_level = is_top_level_export(analysis, target);
        if is_top_level {
            collect_cross_file_edits(state, current_path, old_name, new_name, &mut changes)
        } else {
            None
        }
    } else {
        None
    };

    Some(RenameResult {
        edit: WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        },
        warning,
    })
}

// ==============================================================================
// Cross-file helpers
// ==============================================================================

/// Determine whether `target` is a top-level export of this file.
///
/// A name is considered a top-level export when it appears as a field in
/// the file's root expression (which is typically an attrset or a let-in
/// whose body is an attrset). This covers the common Nix pattern:
///
///   { foo = 1; bar = 2; }         # AttrSet at root
///   let helper = ...; in { ... }  # LetIn whose body is AttrSet
fn is_top_level_export(analysis: &FileSnapshot, target: NameId) -> bool {
    let entry = analysis.syntax.module.entry_expr;
    fields_of_root_attrset(&analysis.syntax.module, entry).is_some_and(|fields| fields.contains(&target))
}

/// Collect NameIds of fields in the root-level attrset, chasing through
/// LetIn bodies (Nix files commonly have `let ... in { fields }` at the top).
fn fields_of_root_attrset(module: &lang_ast::Module, expr_id: ExprId) -> Option<Vec<NameId>> {
    match &module[expr_id] {
        Expr::AttrSet { bindings, .. } => {
            Some(bindings.statics.iter().map(|(name, _)| *name).collect())
        }
        Expr::LetIn { body, .. } => fields_of_root_attrset(module, *body),
        _ => None,
    }
}

/// Scan all open files for imports pointing at `current_path`, and collect
/// TextEdits that rename Select field references from `old_name` to `new_name`.
///
/// Returns a warning message if we detect that some files on disk import the
/// current file but aren't currently open in the editor.
fn collect_cross_file_edits(
    state: &AnalysisState,
    current_path: &PathBuf,
    old_name: &str,
    new_name: &str,
    changes: &mut HashMap<Url, Vec<TextEdit>>,
) -> Option<String> {
    let mut updated_file_count = 0;

    // Walk every open file's name_to_import map looking for entries that
    // point to the file being edited.
    for (other_path, other_analysis) in &state.files {
        // Skip the file itself — its edits are already collected above.
        if other_path == current_path {
            continue;
        }

        // Collect NameIds in this file that are bound to imports of the target file.
        let importing_names: Vec<NameId> = other_analysis
            .name_to_import
            .iter()
            .filter(|(_, path)| *path == current_path)
            .map(|(name_id, _)| *name_id)
            .collect();

        if importing_names.is_empty() {
            continue;
        }

        // Find Select expressions in this file that:
        //  1. Have a base expression resolving to one of the importing_names
        //  2. Have a first attrpath segment matching old_name
        let other_root = other_analysis.parsed.tree();
        let mut file_edits = Vec::new();

        for (_expr_id, expr) in other_analysis.module.exprs() {
            if let Expr::Select { set, attrpath, .. } = expr {
                // Resolve the Select's base to a NameId.
                if let Some(base_name) =
                    resolve_to_name(&other_analysis.module, &other_analysis.name_res, *set)
                {
                    if importing_names.contains(&base_name) {
                        // Check the first attrpath segment.
                        if let Some(&first_attr_expr) = attrpath.first() {
                            if matches!(
                                &other_analysis.module[first_attr_expr],
                                Expr::Literal(Literal::String(s)) if s.as_str() == old_name
                            ) {
                                if let Some(ptr) =
                                    other_analysis.source_map.node_for_expr(first_attr_expr)
                                {
                                    let node = ptr.to_node(other_root.syntax());
                                    let range = other_analysis.line_index.range(node.text_range());
                                    file_edits.push(TextEdit {
                                        range,
                                        new_text: new_name.to_string(),
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // Also check HasAttr expressions (`x ? oldName`), which reference
            // field names the same way Select does.
            if let Expr::HasAttr { set, attrpath } = expr {
                if let Some(base_name) =
                    resolve_to_name(&other_analysis.module, &other_analysis.name_res, *set)
                {
                    if importing_names.contains(&base_name) {
                        if let Some(&first_attr_expr) = attrpath.first() {
                            if matches!(
                                &other_analysis.module[first_attr_expr],
                                Expr::Literal(Literal::String(s)) if s.as_str() == old_name
                            ) {
                                if let Some(ptr) =
                                    other_analysis.source_map.node_for_expr(first_attr_expr)
                                {
                                    let node = ptr.to_node(other_root.syntax());
                                    let range = other_analysis.line_index.range(node.text_range());
                                    file_edits.push(TextEdit {
                                        range,
                                        new_text: new_name.to_string(),
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        if !file_edits.is_empty() {
            updated_file_count += 1;
            if let Ok(other_uri) = Url::from_file_path(other_path) {
                changes.entry(other_uri).or_default().extend(file_edits);
            }
        }
    }

    // Emit a warning when cross-file edits were produced, since there may be
    // additional files on disk (not open in the editor) that also import this
    // file. We can't detect those, so we warn proactively.
    if updated_file_count > 0 {
        Some(format!(
            "Renamed '{old_name}' to '{new_name}' across {updated_file_count} other open file(s). \
             Files not open in the editor that import this file won't be updated."
        ))
    } else {
        None
    }
}

/// Chase a set expression to the NameId it ultimately references.
///
/// Handles the common patterns:
///   - `lib.field`  where `lib` is a Reference -> resolves to lib's NameId
///   - `(import ./foo.nix).field` -> no NameId (returns None)
///
/// Takes `Module` and `NameResolution` directly so it works with both
/// `FileSnapshot` (same-file) and `FileAnalysis` (cross-file) contexts.
fn resolve_to_name(
    module: &lang_ast::Module,
    name_res: &lang_ast::NameResolution,
    expr_id: ExprId,
) -> Option<NameId> {
    if let Expr::Reference(_) = &module[expr_id] {
        if let Some(lang_ast::nameres::ResolveResult::Definition(name_id)) = name_res.get(expr_id)
        {
            return Some(*name_id);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TempProject, TestAnalysis};
    use indoc::indoc;
    use lang_check::aliases::TypeAliasRegistry;

    // Helper for single-file rename tests (no cross-file context).
    fn rename_at_marker(src: &str, marker: u32, new_name: &str) -> Option<WorkspaceEdit> {
        let markers = parse_markers(src);
        let offset = markers[&marker];
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();
        let uri = t.uri();
        let pos = analysis.syntax.line_index.position(offset);
        rename(&analysis, pos, new_name, &uri, &t.root, None, None).map(|r| r.edit)
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
        let analysis = t.snapshot();
        let pos = analysis.syntax.line_index.position(offset);

        assert!(prepare_rename(&analysis, pos, &t.root).is_none());
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

    // ==========================================================================
    // Cross-file rename tests
    // ==========================================================================

    /// Helper: set up a multi-file project, analyze all files, then rename at
    /// a marker in the first file. Returns the RenameResult.
    fn cross_file_rename(
        files: &[(&str, &str)],
        rename_file: &str,
        marker: u32,
        new_name: &str,
    ) -> Option<RenameResult> {
        let project = TempProject::new(files);

        // Analyze all files (order matters: imported files must be analyzed
        // before importers for import resolution to work, but for our purpose
        // we just need all files in state.files).
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        for (name, contents) in files {
            let path = project.path(name);
            state.update_file(path, contents.to_string());
        }

        let rename_path = project.path(rename_file);
        let analysis = state.get_file(&rename_path).unwrap().to_snapshot();
        let root = analysis.syntax.parsed.tree();

        // Parse markers from the rename file's source.
        let rename_src = files
            .iter()
            .find(|(name, _)| *name == rename_file)
            .unwrap()
            .1;
        let markers = parse_markers(rename_src);
        let offset = markers[&marker];
        let pos = analysis.syntax.line_index.position(offset);
        let uri = Url::from_file_path(&rename_path).unwrap();

        rename(
            &analysis,
            pos,
            new_name,
            &uri,
            &root,
            Some(&state),
            Some(&rename_path),
        )
    }

    #[test]
    fn cross_file_rename_updates_select_in_importer() {
        // lib.nix exports { foo, bar }; main.nix does `lib.foo`.
        // Renaming `foo` in lib.nix should also produce an edit in main.nix.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        { foo = 1; bar = 2; }
                        # ^1
                    "},
                ),
                (
                    "main.nix",
                    "let lib = import ./lib.nix; in lib.foo + lib.bar",
                ),
            ],
            "lib.nix",
            1,
            "qux",
        );

        let result = result.expect("should produce rename result");
        let edit = &result.edit;

        // lib.nix: 1 edit (the definition of `foo`)
        // main.nix: 1 edit (the `foo` in `lib.foo`)
        let total = edit_count(edit);
        assert_eq!(
            total, 2,
            "should have 1 definition edit + 1 cross-file select edit, got {total}"
        );

        // Verify we got edits in two different files.
        let file_count = edit.changes.as_ref().unwrap().len();
        assert_eq!(
            file_count, 2,
            "should have edits in 2 files, got {file_count}"
        );

        // Should produce a warning about potentially un-updated files.
        assert!(
            result.warning.is_some(),
            "should warn about cross-file rename"
        );
    }

    #[test]
    fn cross_file_rename_multiple_references() {
        // main.nix uses `lib.foo` twice.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        { foo = 1; bar = 2; }
                        # ^1
                    "},
                ),
                (
                    "main.nix",
                    "let lib = import ./lib.nix; in lib.foo + lib.foo",
                ),
            ],
            "lib.nix",
            1,
            "qux",
        );

        let result = result.expect("should produce rename result");
        let total = edit_count(&result.edit);
        assert_eq!(
            total, 3,
            "1 def + 2 cross-file references = 3 edits, got {total}"
        );
    }

    #[test]
    fn cross_file_rename_no_effect_for_non_export() {
        // Renaming a let-local binding that's not a top-level export should
        // not produce cross-file edits even if the file is imported.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        let helper = 1; in { foo = helper; }
                        #   ^1
                    "},
                ),
                ("main.nix", "let lib = import ./lib.nix; in lib.foo"),
            ],
            "lib.nix",
            1,
            "renamed_helper",
        );

        let result = result.expect("should produce rename result");
        let total = edit_count(&result.edit);
        // Only local edits: definition of `helper` + reference in `{ foo = helper; }`
        assert_eq!(total, 2, "should only rename locally, got {total}");
        assert!(
            result.warning.is_none(),
            "should not warn for non-export rename"
        );
    }

    #[test]
    fn cross_file_rename_let_in_attrset() {
        // The common `let ... in { exports }` pattern: renaming a field in
        // the body attrset should still count as a top-level export.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        let x = 1; in { foo = x; bar = 2; }
                        #               ^1
                    "},
                ),
                ("main.nix", "let lib = import ./lib.nix; in lib.foo"),
            ],
            "lib.nix",
            1,
            "baz",
        );

        let result = result.expect("should produce rename result");
        let total = edit_count(&result.edit);
        // lib.nix: definition of `foo` + reference to `foo` (there's no local ref, just def)
        // main.nix: `foo` in `lib.foo`
        assert_eq!(total, 2, "1 def + 1 cross-file = 2 edits, got {total}");
    }

    #[test]
    fn cross_file_rename_bar_not_touched() {
        // Renaming `foo` should not affect `bar` references in importers.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        { foo = 1; bar = 2; }
                        # ^1
                    "},
                ),
                ("main.nix", "let lib = import ./lib.nix; in lib.bar"),
            ],
            "lib.nix",
            1,
            "qux",
        );

        let result = result.expect("should produce rename result");
        let total = edit_count(&result.edit);
        // Only the definition of `foo` in lib.nix — no cross-file edits.
        assert_eq!(total, 1, "should only rename definition, got {total}");
    }

    #[test]
    fn cross_file_rename_with_has_attr() {
        // `lib ? foo` should also be renamed when `foo` is renamed.
        let result = cross_file_rename(
            &[
                (
                    "lib.nix",
                    indoc! {"
                        { foo = 1; }
                        # ^1
                    "},
                ),
                (
                    "main.nix",
                    "let lib = import ./lib.nix; in if lib ? foo then lib.foo else null",
                ),
            ],
            "lib.nix",
            1,
            "qux",
        );

        let result = result.expect("should produce rename result");
        let total = edit_count(&result.edit);
        // 1 def in lib.nix + 2 cross-file (lib ? foo + lib.foo) = 3
        assert_eq!(
            total, 3,
            "1 def + 1 HasAttr + 1 Select = 3 edits, got {total}"
        );
    }

    #[test]
    fn is_top_level_export_basic_attrset() {
        let src = "{ foo = 1; bar = 2; }";
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();

        // All fields of a top-level attrset should be top-level exports.
        for (name_id, name) in analysis.syntax.module.names() {
            assert!(
                is_top_level_export(&analysis, name_id),
                "{} should be a top-level export",
                name.text
            );
        }
    }

    #[test]
    fn is_top_level_export_let_in_attrset() {
        let src = "let helper = 1; in { foo = helper; }";
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();

        for (name_id, name) in analysis.syntax.module.names() {
            let expected = name.text == "foo";
            assert_eq!(
                is_top_level_export(&analysis, name_id),
                expected,
                "{} export status should be {expected}",
                name.text
            );
        }
    }

    #[test]
    fn is_top_level_export_lambda_not_export() {
        // A file whose top-level expression is a lambda — its param is not
        // an "export" in the attrset sense.
        let src = "x: x + 1";
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();

        for (name_id, name) in analysis.syntax.module.names() {
            assert!(
                !is_top_level_export(&analysis, name_id),
                "{} should NOT be a top-level export",
                name.text
            );
        }
    }
}
