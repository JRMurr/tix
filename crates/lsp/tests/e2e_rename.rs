mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// prepareRename returns a range and placeholder text.
#[tokio::test]
async fn prepare_rename_returns_range() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let foo = 1; in foo
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let result = h
        .prepare_rename("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("prepareRename should return a result");

    // Should contain range info and the current name as placeholder.
    match result {
        PrepareRenameResponse::Range(range) => {
            assert!(range.start.line == m[&1].line);
        }
        PrepareRenameResponse::RangeWithPlaceholder { range, placeholder } => {
            assert!(range.start.line == m[&1].line);
            assert_eq!(placeholder, "foo");
        }
        PrepareRenameResponse::DefaultBehavior { .. } => {
            // Also acceptable — server uses default behavior.
        }
    }

    h.shutdown().await;
}

/// Rename within a single file produces correct edits for def + refs.
#[tokio::test]
async fn rename_single_file() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let foo = 1; in foo + foo
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let edit = h
        .rename("test.nix", m[&1].line, m[&1].character, "bar")
        .await
        .expect("rename should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let test_uri = Url::from_file_path(h.workspace.path("test.nix")).unwrap();
    let edits = changes
        .get(&test_uri)
        .expect("should have edits for test.nix");

    // Definition + 2 references = 3 edits, all replacing "foo" with "bar".
    assert_eq!(
        edits.len(),
        3,
        "expected 3 rename edits, got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "bar");
    }

    h.shutdown().await;
}

/// Rename across files: edits span both file URIs.
#[tokio::test]
async fn rename_cross_file() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ val = 42; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                #   ^1
                in a.val
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");

    let edit = h
        .rename("b.nix", m[&1].line, m[&1].character, "lib")
        .await
        .expect("rename should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let b_uri = Url::from_file_path(h.workspace.path("b.nix")).unwrap();
    let edits = changes.get(&b_uri).expect("should have edits for b.nix");

    // `a` is used at the let-binding and in `a.val` — at least 2 edits.
    assert!(
        edits.len() >= 2,
        "expected at least 2 rename edits in b.nix, got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "lib");
    }

    h.shutdown().await;
}
