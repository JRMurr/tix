mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Background analysis processes files from [project] includes globs
/// without the user explicitly opening them.
///
/// This test creates a workspace with a tix.toml that specifies includes
/// globs, verifies diagnostics are published for background files, and
/// then checks that opening a file that imports a background-analyzed
/// file gets the correct cross-file type.
#[tokio::test]
async fn background_analysis_processes_queued_files() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {r#"
                [project]
                includes = ["lib/*.nix"]
            "#},
        ),
        // This file is matched by the includes glob — it should be
        // background-analyzed without being explicitly opened.
        ("lib/helpers.nix", "{ greet = \"hello\"; count = 42; }"),
    ])
    .await;

    // Don't open any files. Wait for background analysis to publish
    // diagnostics for lib/helpers.nix.
    let diags = h.wait_for_diagnostics("lib/helpers.nix", TIMEOUT).await;
    assert!(
        diags.is_some(),
        "expected diagnostics for background-analyzed lib/helpers.nix"
    );

    h.shutdown().await;
}

/// After background analysis completes, opening a file that imports a
/// background-analyzed file should resolve the import type from the
/// coordinator cache (not ⊤).
#[tokio::test]
async fn background_analysis_populates_import_cache() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {r#"
                [project]
                includes = ["lib/*.nix"]
            "#},
        ),
        ("lib/helpers.nix", "{ greet = \"hello\"; count = 42; }"),
        (
            "main.nix",
            indoc! {"
                let h = import ./lib/helpers.nix;
                in h.count
                #    ^1
            "},
        ),
    ])
    .await;

    // Wait for background analysis to complete lib/helpers.nix.
    let _ = h.wait_for_diagnostics("lib/helpers.nix", TIMEOUT).await;

    // Now open main.nix — the import should resolve from the cache.
    h.open("main.nix").await;
    let _ = h.wait_for_diagnostics("main.nix", TIMEOUT).await;

    let m = h.markers("main.nix");
    let hover = h.hover("main.nix", m[&1].line, m[&1].character).await;
    let hover_text = match hover {
        Some(Hover {
            contents: HoverContents::Markup(MarkupContent { value, .. }),
            ..
        }) => value,
        other => panic!("expected markup hover, got {other:?}"),
    };

    // h.count should be inferred as int (from the background-analyzed helpers.nix),
    // not ⊤ (which would show as ? or top).
    assert!(
        hover_text.contains("int"),
        "expected 'int' in hover for h.count, got: {hover_text}"
    );

    h.shutdown().await;
}
