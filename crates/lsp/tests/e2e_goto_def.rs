mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Go-to-definition on a let-binding reference resolves to the definition site.
#[tokio::test]
async fn goto_def_same_file() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
            #   ^1         ^2
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    // Go-to-def on the reference `x` should jump to the definition.
    let result = h
        .goto_def("test.nix", m[&2].line, m[&2].character)
        .await
        .expect("goto_def should return a result");

    let target_pos = match result {
        GotoDefinitionResponse::Scalar(loc) => loc.range.start,
        GotoDefinitionResponse::Array(locs) => locs[0].range.start,
        GotoDefinitionResponse::Link(links) => links[0].target_range.start,
    };

    assert_eq!(
        target_pos, m[&1],
        "goto_def should point to the definition of x"
    );

    h.shutdown().await;
}

/// Go-to-definition across files: `a.x` in b.nix resolves into a.nix.
#[tokio::test]
async fn goto_def_cross_file() {
    let mut h = LspTestHarness::new(&[
        (
            "a.nix",
            indoc! {"
                { x = 42; }
                # ^1
            "},
        ),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.x
                #    ^2
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m_b = h.markers("b.nix");

    let result = h
        .goto_def("b.nix", m_b[&2].line, m_b[&2].character)
        .await
        .expect("goto_def should return a cross-file result");

    // The target should be in a.nix, not b.nix.
    let target_uri = match &result {
        GotoDefinitionResponse::Scalar(loc) => &loc.uri,
        GotoDefinitionResponse::Array(locs) => &locs[0].uri,
        GotoDefinitionResponse::Link(links) => &links[0].target_uri,
    };

    let a_uri = Url::from_file_path(h.workspace.path("a.nix")).unwrap();
    assert_eq!(target_uri, &a_uri, "goto_def target should be in a.nix");

    h.shutdown().await;
}
