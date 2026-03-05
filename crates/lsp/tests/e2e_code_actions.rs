mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Missing field diagnostic produces an "Add missing field" quick fix.
#[tokio::test]
async fn missing_field_quick_fix() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = { foo = 1; }; in x.bar
            #                          ^1
        "},
    )])
    .await;

    h.open("test.nix").await;

    // Wait for diagnostics — we need them to drive the code action.
    let diag_params = h
        .wait_for_diagnostics("test.nix", TIMEOUT)
        .await
        .expect("should get diagnostics");

    let m = h.markers("test.nix");

    // Use the marker position as the range for the code action request.
    let range = Range::new(m[&1], m[&1]);

    let actions = h
        .code_actions("test.nix", range, diag_params.diagnostics)
        .await
        .expect("code_actions should return results");

    let titles: Vec<String> = actions
        .iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(ca) => Some(ca.title.clone()),
            _ => None,
        })
        .collect();

    assert!(
        titles.iter().any(|t| t.contains("Add missing field")),
        "should offer 'Add missing field' action, got: {titles:?}"
    );

    h.shutdown().await;
}

/// Unused let-binding produces a "Remove unused binding" quick fix.
#[tokio::test]
async fn remove_unused_binding() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let unused = 1; used = 2; in used
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let range = Range::new(m[&1], m[&1]);

    let actions = h
        .code_actions("test.nix", range, vec![])
        .await
        .expect("code_actions should return results");

    let titles: Vec<String> = actions
        .iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(ca) => Some(ca.title.clone()),
            _ => None,
        })
        .collect();

    assert!(
        titles.iter().any(|t| t.contains("Remove unused binding")),
        "should offer 'Remove unused binding' action, got: {titles:?}"
    );

    h.shutdown().await;
}
