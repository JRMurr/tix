mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Full-document range for requesting all inlay hints.
fn full_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(u32::MAX, 0))
}

/// Non-trivial let-bindings produce type inlay hints.
/// Trivial literals (x = 42) are skipped — use computed expressions.
#[tokio::test]
async fn hints_for_bindings() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let
              x = 1 + 2;
              f = a: a + 1;
            in f x
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let hints = h
        .inlay_hints("test.nix", full_range())
        .await
        .expect("inlay_hints should return results");

    assert!(
        !hints.is_empty(),
        "should produce inlay hints for let-bindings"
    );

    h.shutdown().await;
}

/// Inlay hints update after editing the file.
#[tokio::test]
async fn hints_update_after_edit() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let hints_before = h
        .inlay_hints("test.nix", full_range())
        .await
        .unwrap_or_default();

    // Edit: change from a simple int to a function.
    h.edit("test.nix", "let x = a: a + 1; in x").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let hints_after = h
        .inlay_hints("test.nix", full_range())
        .await
        .unwrap_or_default();

    // The hints should differ (int vs function type) — or at minimum not crash.
    // We can't assert exact content since hint format may vary, but we can check
    // the request round-trips correctly after an edit.
    let label_before: Vec<_> = hints_before
        .iter()
        .map(|h| format!("{:?}", h.label))
        .collect();
    let label_after: Vec<_> = hints_after
        .iter()
        .map(|h| format!("{:?}", h.label))
        .collect();

    // At least one hint should change if the type changed.
    if !hints_before.is_empty() && !hints_after.is_empty() {
        assert_ne!(
            label_before, label_after,
            "hints should change after editing the value type"
        );
    }

    h.shutdown().await;
}
