mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Dot completion shows attrset fields after analysis completes.
#[tokio::test]
async fn dot_completion_after_analysis() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let lib = { id = x: x; add = x: y: x + y; };
            in lib.
            #      ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let completions = h
        .complete("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("completion should return results");

    let items = match completions {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };

    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    assert!(
        labels.contains(&"id"),
        "should complete 'id', got: {labels:?}"
    );
    assert!(
        labels.contains(&"add"),
        "should complete 'add', got: {labels:?}"
    );

    h.shutdown().await;
}

/// Completion before analysis completes should still return something
/// (at minimum, a parse-only completion or no crash).
#[tokio::test]
async fn completion_before_analysis_no_crash() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let lib = { foo = 1; bar = 2; };
            in lib.
            #      ^1
        "},
    )])
    .await;

    h.open("test.nix").await;

    // Request completion immediately — don't wait for diagnostics.
    let m = h.markers("test.nix");
    let _completions = h.complete("test.nix", m[&1].line, m[&1].character).await;
    // We don't assert specific items here — the point is that it doesn't crash.

    h.shutdown().await;
}

/// Completion at a let-binding reference position should include bound names.
#[tokio::test]
async fn let_binding_completion() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let alpha = 1; beta = 2; gamma = 3;
            in a
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let completions = h
        .complete("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("completion should return results");

    let items = match completions {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };

    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    assert!(
        labels.contains(&"alpha"),
        "should complete 'alpha', got: {labels:?}"
    );

    h.shutdown().await;
}
