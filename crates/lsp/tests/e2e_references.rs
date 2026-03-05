mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// Find references with includeDeclaration returns definition + all uses.
#[tokio::test]
async fn references_include_declaration() {
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

    let refs = h
        .references("test.nix", m[&1].line, m[&1].character, true)
        .await
        .expect("references should return results");

    // Definition + 2 uses = 3 locations.
    assert_eq!(
        refs.len(),
        3,
        "expected 3 references (1 def + 2 uses), got: {}",
        refs.len()
    );

    h.shutdown().await;
}

/// Find references without includeDeclaration returns only use sites.
#[tokio::test]
async fn references_exclude_declaration() {
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

    let refs = h
        .references("test.nix", m[&1].line, m[&1].character, false)
        .await
        .expect("references should return results");

    // 2 uses only, no declaration.
    assert_eq!(
        refs.len(),
        2,
        "expected 2 references (uses only), got: {}",
        refs.len()
    );

    h.shutdown().await;
}
