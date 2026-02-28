mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// Open a file with an error → diagnostics arrive → fix → diagnostics clear.
/// This is the core temporal test that unit tests can't exercise.
#[tokio::test]
async fn diagnostics_appear_and_clear() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        // Unresolved reference `y` → should produce a warning.
        "let x = y; in x",
    )])
    .await;

    h.open("test.nix").await;

    // Wait for diagnostics with the error.
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();
    assert!(
        !diags.diagnostics.is_empty(),
        "expected diagnostics for unresolved `y`, got none"
    );
    assert!(diags.diagnostics.iter().any(|d| d.message.contains("y")));

    // Fix the error: replace `y` with a valid expression.
    h.edit("test.nix", "let x = 42; in x").await;

    // Wait for updated diagnostics — should be empty now.
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();
    assert!(
        diags.diagnostics.is_empty(),
        "expected no diagnostics after fix, got: {:?}",
        diags.diagnostics,
    );

    h.shutdown().await;
}

/// Rapid edits should coalesce — only the final state's diagnostics matter.
#[tokio::test]
async fn rapid_edits_coalesce() {
    let mut h = LspTestHarness::new(&[("test.nix", "1")]).await;
    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    // Send 10 rapid edits without waiting for diagnostics between them.
    for i in 0..10 {
        let text = format!("let x{i} = {i}; in x{i}");
        h.edit("test.nix", &text).await;
    }

    // Wait for the final diagnostics to arrive.
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();

    // All edits are valid Nix, so the final diagnostics should be empty.
    assert!(
        diags.diagnostics.is_empty(),
        "expected clean diagnostics after rapid edits, got: {:?}",
        diags.diagnostics,
    );

    h.shutdown().await;
}

/// Closing a file with errors should publish empty diagnostics.
#[tokio::test]
async fn close_clears_diagnostics() {
    let mut h = LspTestHarness::new(&[("test.nix", "let x = undefined_var; in x")]).await;

    h.open("test.nix").await;

    // Wait for the error diagnostics.
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();
    assert!(!diags.diagnostics.is_empty());

    // Close the file — server should publish empty diagnostics.
    h.close("test.nix").await;

    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();
    assert!(
        diags.diagnostics.is_empty(),
        "expected diagnostics cleared on close, got: {:?}",
        diags.diagnostics,
    );

    h.shutdown().await;
}

/// Duplicate key diagnostic should have related information pointing to
/// the first definition.
#[tokio::test]
async fn duplicate_key_diagnostic() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = { a = 1; a = 2; }; in x
        "},
    )])
    .await;

    h.open("test.nix").await;
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await.unwrap();

    assert!(
        !diags.diagnostics.is_empty(),
        "expected duplicate key diagnostic"
    );

    let dup_diag = diags
        .diagnostics
        .iter()
        .find(|d| d.message.contains("duplicate"))
        .expect("should have a 'duplicate key' diagnostic");

    // The diagnostic should have related_information pointing to the first definition.
    assert!(
        dup_diag.related_information.is_some(),
        "duplicate key diagnostic should have related_information"
    );

    let related = dup_diag.related_information.as_ref().unwrap();
    assert!(
        related.iter().any(|r| r.message.contains("first defined")),
        "related info should mention 'first defined'"
    );

    h.shutdown().await;
}
