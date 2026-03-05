mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Semantic tokens returns non-empty delta-encoded data for a basic file.
#[tokio::test]
async fn tokens_basic() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let result = h
        .semantic_tokens("test.nix")
        .await
        .expect("semantic_tokens should return a result");

    match result {
        SemanticTokensResult::Tokens(tokens) => {
            assert!(
                !tokens.data.is_empty(),
                "semantic tokens data should be non-empty"
            );
        }
        SemanticTokensResult::Partial(partial) => {
            assert!(
                !partial.data.is_empty(),
                "partial semantic tokens data should be non-empty"
            );
        }
    }

    h.shutdown().await;
}
