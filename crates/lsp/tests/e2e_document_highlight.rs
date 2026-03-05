mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Document highlight marks the definition and reference sites of a symbol.
#[tokio::test]
async fn highlight_def_and_refs() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 1; in x + x
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let highlights = h
        .document_highlight("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("document_highlight should return results");

    // Definition + 2 references = 3 highlights.
    assert_eq!(
        highlights.len(),
        3,
        "expected 3 highlights (1 def + 2 refs), got: {}",
        highlights.len()
    );

    // At least one should be a WRITE (the definition) and at least one READ (usage).
    let has_write = highlights
        .iter()
        .any(|h| h.kind == Some(DocumentHighlightKind::WRITE));
    let has_read = highlights
        .iter()
        .any(|h| h.kind == Some(DocumentHighlightKind::READ));

    assert!(
        has_write,
        "should have a WRITE highlight for the definition"
    );
    assert!(has_read, "should have a READ highlight for a reference");

    h.shutdown().await;
}
