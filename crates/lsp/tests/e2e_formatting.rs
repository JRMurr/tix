mod common;

use common::{LspTestHarness, TIMEOUT};

/// Formatting returns TextEdits when nixfmt reformats the document.
///
/// This test assumes `nixfmt` is available in the environment (nix devShell).
/// The input is intentionally poorly formatted so nixfmt produces changes.
#[tokio::test]
async fn formatting_returns_edits() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        // Intentionally ugly formatting — extra spaces, no final newline.
        "let   x  =   42;    in    x",
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let edits = h.formatting("test.nix").await;

    // nixfmt should reformat the ugly input into something different.
    let edits = edits.expect("formatting should return edits for poorly formatted input");
    assert!(
        !edits.is_empty(),
        "should have at least one TextEdit from formatting"
    );

    // The edit should contain reformatted text (nixfmt would normalize spacing).
    let new_text = &edits[0].new_text;
    assert!(
        new_text.contains("let") && new_text.contains("in"),
        "formatted text should still contain let/in, got: {new_text}"
    );

    h.shutdown().await;
}
