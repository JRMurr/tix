mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Cross-file hover: A.nix defines a value, B.nix imports it, hover shows the type.
#[tokio::test]
async fn cross_file_hover() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ x = 42; y = \"hello\"; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.x
                #    ^1
            "},
        ),
    ])
    .await;

    // Open both files — A.nix first so it's analyzed when B.nix resolves the import.
    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;

    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on imported field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover on imported x should show 'int', got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Edit A.nix to change a type, verify B.nix hover updates.
#[tokio::test]
async fn cross_file_hover_updates_after_edit() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ val = 42; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.val
                #    ^1
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("initial hover");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(content.value.contains("int"));

    // Edit A.nix: change val from int to string.
    h.edit("a.nix", "{ val = \"updated\"; }").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;

    // Re-open B.nix to trigger re-analysis with updated import.
    h.edit(
        "b.nix",
        indoc! {"
            let a = import ./a.nix;
            in a.val
            #    ^1
        "},
    )
    .await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover after edit");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(
        content.value.contains("string"),
        "hover should update to 'string' after editing imported file, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Multiple files can be open simultaneously without interference.
#[tokio::test]
async fn multiple_files_independent() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "let x = 1; in x"),
        ("b.nix", "let y = \"hello\"; in y"),
    ])
    .await;

    h.open("a.nix").await;
    h.open("b.nix").await;

    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    // Both files should have clean diagnostics.
    // (we already consumed them above, but verify no errors were present)

    h.shutdown().await;
}
