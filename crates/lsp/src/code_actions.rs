// ==============================================================================
// textDocument/codeAction — quick fixes and refactors
// ==============================================================================
//
// Provides code actions triggered by diagnostics or cursor position:
//
// 1. "Add missing field" — when a MissingField diagnostic exists on a Select
//    expression, offers to add the field with a placeholder value to the attrset
//    definition being selected from.
//
// 2. "Add type annotation" — when the cursor is on a let-binding name with an
//    inferred type, offers to insert a doc comment annotation above the binding.
//
// 3. "Remove unused binding" — when a let-binding has no references, offers to
//    remove the entire binding (name = value;).

use lang_ast::{Expr, NameKind};
use lang_check::diagnostic::TixDiagnosticKind;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::*;

use crate::state::FileAnalysis;

/// Compute code actions for the given range in the document.
///
/// The LSP client sends the cursor range and any diagnostics the editor shows
/// at that range. We match diagnostics to produce quick-fix actions and also
/// offer refactoring actions based on the cursor position.
pub fn code_actions(
    analysis: &FileAnalysis,
    params: &CodeActionParams,
    root: &rnix::Root,
) -> Vec<CodeActionOrCommand> {
    let mut actions = Vec::new();
    let uri = &params.text_document.uri;

    // -- Diagnostic-driven actions --
    add_missing_field_actions(analysis, params, root, uri, &mut actions);

    // -- Position-driven actions --
    add_type_annotation_actions(analysis, params, root, uri, &mut actions);
    remove_unused_binding_actions(analysis, params, root, uri, &mut actions);

    actions
}

// ==============================================================================
// "Add missing field" quick fix
// ==============================================================================
//
// When a MissingField diagnostic is present, the `at_expr` points to the
// attrpath literal (e.g. `bar` in `x.bar`) -- the expression that was being
// inferred when the field-presence constraint was created. We find the
// enclosing Select expression to locate the attrset definition being accessed,
// then offer to insert `field = <placeholder>;` at the end of that attrset.
//
// This only works when:
//   - We can find a Select expression whose attrpath contains `at_expr`
//   - The Select's `set` is a Reference that resolves to a name
//   - That name's binding expression is an AttrSet
//   - We can find the closing `}` of the attrset in the source

fn add_missing_field_actions(
    analysis: &FileAnalysis,
    params: &CodeActionParams,
    root: &rnix::Root,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let request_range = params.range;

    for diag in &analysis.check_result.diagnostics {
        let field_name = match &diag.kind {
            TixDiagnosticKind::MissingField { field, .. } => field.clone(),
            _ => continue,
        };

        // Find the source range of the diagnostic expression.
        let diag_range = match analysis.source_map.node_for_expr(diag.at_expr) {
            Some(ptr) => {
                let node = ptr.to_node(root.syntax());
                analysis.line_index.range(node.text_range())
            }
            None => continue,
        };

        // Only offer actions for diagnostics that overlap with the requested range.
        if !ranges_overlap(diag_range, request_range) {
            continue;
        }

        // The `at_expr` typically points to the attrpath literal (e.g. `bar`
        // in `x.bar`), not the Select itself. Find the enclosing Select to
        // get the `set` expression that we need to modify.
        let insert_info = find_enclosing_select_set(analysis, diag.at_expr)
            .and_then(|set_expr| find_attrset_insert_point(analysis, set_expr, root));

        let edit = if let Some((insert_pos, indent)) = insert_info {
            // Insert `field = <placeholder>;` before the closing `}` of the attrset.
            let new_text = format!("{indent}{field_name} = throw \"TODO\";\n");
            let insert_range = Range::new(insert_pos, insert_pos);
            TextEdit {
                range: insert_range,
                new_text,
            }
        } else {
            // Cannot find the attrset definition — skip this action.
            continue;
        };

        let mut changes = std::collections::HashMap::new();
        changes.insert(uri.clone(), vec![edit]);

        // Build an LSP Diagnostic to associate this action with, so editors show
        // it as a quick fix for the specific diagnostic.
        let lsp_diag = Diagnostic {
            range: diag_range,
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("tix".to_string()),
            message: diag.kind.to_string(),
            ..Default::default()
        };

        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: format!("Add missing field `{field_name}`"),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![lsp_diag]),
            edit: Some(WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
            ..Default::default()
        }));
    }
}

/// Find the `set` ExprId of the Select expression that contains `attr_expr`
/// in its attrpath.
///
/// The MissingField diagnostic's `at_expr` points to the attrpath literal
/// (e.g. the `bar` in `x.bar`). We need the Select's `set` to find the
/// attrset definition. This scans all expressions for a Select whose
/// attrpath includes `attr_expr`.
fn find_enclosing_select_set(
    analysis: &FileAnalysis,
    attr_expr: lang_ast::ExprId,
) -> Option<lang_ast::ExprId> {
    for (expr_id, expr) in analysis.module.exprs() {
        if let Expr::Select { set, attrpath, .. } = expr {
            if attrpath.contains(&attr_expr) {
                return Some(*set);
            }
        }
        // Also check if at_expr IS the Select expression directly (defensive).
        if expr_id == attr_expr {
            if let Expr::Select { set, .. } = expr {
                return Some(*set);
            }
        }
    }
    None
}

/// Find the insertion point for a new field in an attrset definition.
///
/// Given the `set` ExprId of a Select (the thing being accessed), chase through
/// name resolution to find the attrset literal, then locate the closing `}` in
/// the source. Returns the position just before `}` and the indentation string
/// for the new field.
fn find_attrset_insert_point(
    analysis: &FileAnalysis,
    set_expr: lang_ast::ExprId,
    root: &rnix::Root,
) -> Option<(Position, String)> {
    // If the set is a Reference, resolve it to the name's binding expression.
    let attrset_expr = match &analysis.module[set_expr] {
        Expr::Reference(_) => {
            let name_id = analysis
                .name_res
                .get(set_expr)
                .and_then(|r| match r {
                    lang_ast::nameres::ResolveResult::Definition(n) => Some(*n),
                    _ => None,
                })?;
            *analysis.module_indices.binding_expr.get(&name_id)?
        }
        // If it's already an AttrSet literal, use it directly.
        Expr::AttrSet { .. } => set_expr,
        _ => return None,
    };

    // Verify this is an AttrSet expression.
    if !matches!(&analysis.module[attrset_expr], Expr::AttrSet { .. }) {
        return None;
    }

    // Find the syntax node for the attrset expression.
    let ptr = analysis.source_map.node_for_expr(attrset_expr)?;
    let node = ptr.to_node(root.syntax());

    // Find the closing `}` token in the attrset node.
    let close_brace = node
        .children_with_tokens()
        .filter_map(|c| c.into_token())
        .find(|t| t.text() == "}")?;

    let close_pos = analysis
        .line_index
        .position(close_brace.text_range().start().into());

    // Determine the indentation of existing fields. Look at the first
    // AttrpathValue child to match the indentation of existing entries.
    let indent = node
        .children()
        .find_map(|child| {
            if rnix::ast::AttrpathValue::can_cast(child.kind())
                || rnix::ast::Inherit::can_cast(child.kind())
            {
                let start = child.text_range().start();
                let start_pos = analysis.line_index.position(start.into());
                Some(" ".repeat(start_pos.character as usize))
            } else {
                None
            }
        })
        // Fallback: use 2-space indent relative to the open brace.
        .unwrap_or_else(|| {
            let open_pos = analysis
                .line_index
                .position(node.text_range().start().into());
            " ".repeat(open_pos.character as usize + 2)
        });

    Some((close_pos, indent))
}

// ==============================================================================
// "Add type annotation" refactoring
// ==============================================================================
//
// When the cursor is on a let-binding name that has an inferred type, offers to
// insert a `/** type: name :: <type> */` doc comment above the binding.

fn add_type_annotation_actions(
    analysis: &FileAnalysis,
    params: &CodeActionParams,
    root: &rnix::Root,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let inference = match analysis.inference() {
        Some(inf) => inf,
        None => return,
    };

    let request_range = params.range;

    for (name_id, name) in analysis.module.names() {
        // Only offer annotations for let-bindings and rec-attrset fields.
        if !matches!(name.kind, NameKind::LetIn | NameKind::RecAttrset) {
            continue;
        }

        // Get the name's source position.
        let ptr = match analysis.source_map.nodes_for_name(name_id).next() {
            Some(p) => p,
            None => continue,
        };
        let node = ptr.to_node(root.syntax());
        let name_range = analysis.line_index.range(node.text_range());

        // Only offer when the cursor overlaps the name.
        if !ranges_overlap(name_range, request_range) {
            continue;
        }

        // Look up the inferred type.
        let ty = match inference.name_ty_map.get(name_id) {
            Some(t) => t,
            None => continue,
        };

        // Skip if there's already a doc comment annotation for this name.
        // Check if the binding's AttrpathValue or LetIn entry already has a
        // preceding doc comment with `type:`.
        if has_existing_annotation(&node) {
            continue;
        }

        let ty_str = ty.to_string();
        let name_text = &name.text;

        // Insert position: start of the line containing the name binding.
        // The annotation goes on the line above.
        let binding_line = name_range.start.line;
        let indent = " ".repeat(name_range.start.character as usize);
        let annotation = format!("{indent}/** type: {name_text} :: {ty_str} */\n");

        let insert_pos = Position::new(binding_line, 0);
        let insert_range = Range::new(insert_pos, insert_pos);

        let edit = TextEdit {
            range: insert_range,
            new_text: annotation,
        };

        let mut changes = std::collections::HashMap::new();
        changes.insert(uri.clone(), vec![edit]);

        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: format!("Add type annotation for `{name_text}`"),
            kind: Some(CodeActionKind::REFACTOR),
            edit: Some(WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
            ..Default::default()
        }));
    }
}

/// Check whether the syntax node already has a doc comment annotation.
///
/// Walks backward through preceding siblings/tokens looking for a comment
/// that contains `type:`.
fn has_existing_annotation(name_node: &rnix::SyntaxNode) -> bool {
    // Walk up to find the AttrpathValue or the let-binding parent.
    let binding_node = name_node.ancestors().find(|n| {
        rnix::ast::AttrpathValue::can_cast(n.kind()) || rnix::ast::LetIn::can_cast(n.kind())
    });

    let binding_node = match binding_node {
        Some(n) => n,
        None => return false,
    };

    // For AttrpathValue, check preceding siblings for doc comments.
    // For LetIn, look at children before the first binding.
    for sibling in binding_node.children_with_tokens() {
        if let Some(token) = sibling.as_token() {
            let text = token.text();
            if text.contains("/**") && text.contains("type:") {
                return true;
            }
        }
    }

    // Also check tokens immediately before the binding node.
    let mut prev = binding_node.prev_sibling_or_token();
    while let Some(el) = prev {
        match el {
            rowan::NodeOrToken::Token(ref token) => {
                let text = token.text();
                if text.contains("/**") && text.contains("type:") {
                    return true;
                }
                // Stop at non-whitespace, non-comment tokens.
                if !text.trim().is_empty()
                    && !text.starts_with('#')
                    && !text.starts_with("/*")
                {
                    break;
                }
            }
            rowan::NodeOrToken::Node(_) => break,
        }
        prev = el.prev_sibling_or_token();
    }

    false
}

// ==============================================================================
// "Remove unused binding" quick fix
// ==============================================================================
//
// When a let-binding has no references (detected via name resolution's inverted
// index), offers to remove the entire `name = value;` text from the source.

fn remove_unused_binding_actions(
    analysis: &FileAnalysis,
    params: &CodeActionParams,
    root: &rnix::Root,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let request_range = params.range;

    for (name_id, name) in analysis.module.names() {
        // Only consider let-bindings for removal. Attrset fields and params
        // are structural and removing them would change semantics.
        if name.kind != NameKind::LetIn {
            continue;
        }

        // Skip the name if it has any references.
        let refs = analysis.name_res.refs_to(name_id);
        if !refs.is_empty() {
            continue;
        }

        // Skip names starting with underscore — conventional "unused" prefix.
        if name.text.starts_with('_') {
            continue;
        }

        // Get the name's source position.
        let ptr = match analysis.source_map.nodes_for_name(name_id).next() {
            Some(p) => p,
            None => continue,
        };
        let name_node = ptr.to_node(root.syntax());
        let name_range = analysis.line_index.range(name_node.text_range());

        // Only offer when the cursor overlaps the name.
        if !ranges_overlap(name_range, request_range) {
            continue;
        }

        // Find the full binding: walk up to the AttrpathValue node which
        // contains `name = value;`.
        let binding_node = name_node
            .ancestors()
            .find(|n| rnix::ast::AttrpathValue::can_cast(n.kind()));

        let binding_node = match binding_node {
            Some(n) => n,
            None => continue,
        };

        // Compute the range to delete. Include trailing whitespace/newline
        // so we don't leave blank lines.
        let binding_range = binding_node.text_range();
        let mut delete_end = binding_range.end();

        // Extend past trailing whitespace and one newline.
        let syntax_text = root.syntax().text();
        let end_offset = usize::from(delete_end);
        let remaining = &syntax_text.to_string()[end_offset..];
        for ch in remaining.chars() {
            if ch == ' ' || ch == '\t' {
                delete_end += rowan::TextSize::of(ch);
            } else if ch == '\n' {
                delete_end += rowan::TextSize::of(ch);
                break;
            } else {
                break;
            }
        }

        // Also extend backward to consume leading whitespace on the line.
        let mut delete_start = binding_range.start();
        let prefix = &syntax_text.to_string()[..usize::from(delete_start)];
        for ch in prefix.chars().rev() {
            if ch == ' ' || ch == '\t' {
                delete_start -= rowan::TextSize::of(ch);
            } else {
                break;
            }
        }

        let delete_range = Range::new(
            analysis.line_index.position(delete_start.into()),
            analysis.line_index.position(delete_end.into()),
        );

        let edit = TextEdit {
            range: delete_range,
            new_text: String::new(),
        };

        let mut changes = std::collections::HashMap::new();
        changes.insert(uri.clone(), vec![edit]);

        let name_text = &name.text;
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: format!("Remove unused binding `{name_text}`"),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
            is_preferred: Some(false),
            ..Default::default()
        }));
    }
}

// ==============================================================================
// Helpers
// ==============================================================================

/// Check if two LSP ranges overlap (share at least one character position).
fn ranges_overlap(a: Range, b: Range) -> bool {
    a.start <= b.end && b.start <= a.end
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;

    /// Helper: compute code actions at a marker position (zero-width range).
    fn actions_at_marker(src: &str, marker: u32) -> Vec<CodeActionOrCommand> {
        let markers = parse_markers(src);
        let offset = markers[&marker];
        let t = TestAnalysis::new(src);
        let analysis = t.analysis();
        let root = &t.root;
        let pos = analysis.line_index.position(offset);
        let range = Range::new(pos, pos);

        let params = CodeActionParams {
            text_document: TextDocumentIdentifier { uri: t.uri() },
            range,
            context: CodeActionContext {
                diagnostics: vec![],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        code_actions(analysis, &params, root)
    }

    /// Extract titles from code actions.
    fn action_titles(actions: &[CodeActionOrCommand]) -> Vec<String> {
        actions
            .iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(ca) => Some(ca.title.clone()),
                _ => None,
            })
            .collect()
    }

    /// Extract the workspace edit from the first code action with the given title.
    fn edit_for_title(
        actions: &[CodeActionOrCommand],
        title_substring: &str,
    ) -> Option<WorkspaceEdit> {
        actions.iter().find_map(|a| match a {
            CodeActionOrCommand::CodeAction(ca) if ca.title.contains(title_substring) => {
                ca.edit.clone()
            }
            _ => None,
        })
    }

    // ======================================================================
    // "Add missing field" tests
    // ======================================================================

    #[test]
    fn add_missing_field_offers_quick_fix() {
        // The MissingField diagnostic's at_expr points to the attrpath literal
        // (`bar`), so the marker needs to point within that range.
        let src = indoc! {"
            let x = { foo = 1; }; in x.bar
            #                          ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            titles.iter().any(|t| t.contains("Add missing field")),
            "expected 'Add missing field' action, got: {titles:?}"
        );
    }

    #[test]
    fn add_missing_field_inserts_into_attrset() {
        let src = indoc! {"
            let x = { foo = 1; }; in x.bar
            #                          ^1
        "};
        let actions = actions_at_marker(src, 1);
        let edit = edit_for_title(&actions, "Add missing field")
            .expect("should have an edit for missing field");

        // The edit should insert text containing `bar`.
        let changes = edit.changes.unwrap();
        let all_edits: Vec<_> = changes.values().flat_map(|v| v.iter()).collect();
        assert!(!all_edits.is_empty(), "should produce at least one text edit");

        let new_text = &all_edits[0].new_text;
        assert!(
            new_text.contains("bar"),
            "inserted text should contain the field name 'bar', got: {new_text}"
        );
    }

    #[test]
    fn no_missing_field_action_when_field_exists() {
        let src = indoc! {"
            let x = { foo = 1; }; in x.foo
            #                          ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            !titles.iter().any(|t| t.contains("Add missing field")),
            "should not offer 'Add missing field' when field exists, got: {titles:?}"
        );
    }

    // ======================================================================
    // "Add type annotation" tests
    // ======================================================================

    #[test]
    fn add_type_annotation_offers_refactor() {
        let src = indoc! {"
            let x = 42; in x
            #   ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            titles.iter().any(|t| t.contains("Add type annotation")),
            "expected 'Add type annotation' action, got: {titles:?}"
        );
    }

    #[test]
    fn add_type_annotation_inserts_doc_comment() {
        let src = indoc! {"
            let x = 42; in x
            #   ^1
        "};
        let actions = actions_at_marker(src, 1);
        let edit = edit_for_title(&actions, "Add type annotation")
            .expect("should have an edit for type annotation");

        let changes = edit.changes.unwrap();
        let all_edits: Vec<_> = changes.values().flat_map(|v| v.iter()).collect();
        assert!(!all_edits.is_empty());

        let new_text = &all_edits[0].new_text;
        assert!(
            new_text.contains("/** type:"),
            "annotation should contain '/** type:', got: {new_text}"
        );
        assert!(
            new_text.contains("x ::"),
            "annotation should contain 'x ::', got: {new_text}"
        );
        assert!(
            new_text.contains("int"),
            "annotation should contain 'int' for an integer literal, got: {new_text}"
        );
    }

    #[test]
    fn no_type_annotation_for_param() {
        let src = indoc! {"
            x: x + 1
            #^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            !titles.iter().any(|t| t.contains("Add type annotation")),
            "should not offer annotation for lambda params, got: {titles:?}"
        );
    }

    #[test]
    fn no_type_annotation_when_already_annotated() {
        let src = indoc! {"
            let
              /** type: x :: int */
              x = 42;
            # ^1
            in x
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            !titles.iter().any(|t| t.contains("Add type annotation")),
            "should not offer annotation when one already exists, got: {titles:?}"
        );
    }

    // ======================================================================
    // "Remove unused binding" tests
    // ======================================================================

    #[test]
    fn remove_unused_binding_offers_quick_fix() {
        let src = indoc! {"
            let x = 1; y = 2; in y
            #   ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            titles.iter().any(|t| t.contains("Remove unused binding")),
            "expected 'Remove unused binding' action for unreferenced `x`, got: {titles:?}"
        );
    }

    #[test]
    fn no_remove_for_used_binding() {
        let src = indoc! {"
            let x = 1; in x
            #   ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            !titles.iter().any(|t| t.contains("Remove unused binding")),
            "should not offer removal for used binding, got: {titles:?}"
        );
    }

    #[test]
    fn no_remove_for_underscore_prefix() {
        let src = indoc! {"
            let _x = 1; y = 2; in y
            #   ^1
        "};
        let actions = actions_at_marker(src, 1);
        let titles = action_titles(&actions);

        assert!(
            !titles.iter().any(|t| t.contains("Remove unused binding")),
            "should not offer removal for underscore-prefixed names, got: {titles:?}"
        );
    }

    #[test]
    fn remove_unused_binding_deletes_correct_range() {
        let src = indoc! {"
            let
              unused = 42;
            # ^1
              used = 1;
            in used
        "};
        let actions = actions_at_marker(src, 1);
        let edit = edit_for_title(&actions, "Remove unused binding")
            .expect("should have an edit for unused binding removal");

        let changes = edit.changes.unwrap();
        let all_edits: Vec<_> = changes.values().flat_map(|v| v.iter()).collect();
        assert!(!all_edits.is_empty());

        // The edit should be a deletion (empty new_text).
        assert!(
            all_edits[0].new_text.is_empty(),
            "removal edit should have empty new_text, got: {:?}",
            all_edits[0].new_text
        );
    }

    // ======================================================================
    // Range overlap tests
    // ======================================================================

    #[test]
    fn ranges_overlap_same_point() {
        let p = Position::new(0, 5);
        assert!(ranges_overlap(Range::new(p, p), Range::new(p, p)));
    }

    #[test]
    fn ranges_overlap_nested() {
        assert!(ranges_overlap(
            Range::new(Position::new(0, 0), Position::new(0, 10)),
            Range::new(Position::new(0, 3), Position::new(0, 5)),
        ));
    }

    #[test]
    fn ranges_no_overlap() {
        assert!(!ranges_overlap(
            Range::new(Position::new(0, 0), Position::new(0, 3)),
            Range::new(Position::new(0, 5), Position::new(0, 8)),
        ));
    }
}
