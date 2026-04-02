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

/// Find references across files: `helper` in lib.nix should include
/// `lib.helper` usage in a.nix.
#[tokio::test]
async fn cross_file_references() {
    let mut h = LspTestHarness::new(&[
        (
            "lib.nix",
            indoc! {"
                { helper = x: x + 1; }
                # ^1
            "},
        ),
        ("a.nix", "let lib = import ./lib.nix; in lib.helper 42"),
    ])
    .await;

    h.open("lib.nix").await;
    let _ = h.wait_for_diagnostics("lib.nix", TIMEOUT).await;
    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;

    let m = h.markers("lib.nix");
    let refs = h
        .references("lib.nix", m[&1].line, m[&1].character, true)
        .await
        .expect("references should return results");

    // 1 declaration in lib.nix + 1 cross-file usage in a.nix = 2
    let a_uri = tower_lsp::lsp_types::Url::from_file_path(h.workspace.path("a.nix")).unwrap();
    let has_cross_file = refs.iter().any(|loc| loc.uri == a_uri);
    assert!(
        has_cross_file,
        "expected a reference in a.nix, got: {refs:?}"
    );
    assert!(
        refs.len() >= 2,
        "expected at least 2 references (1 decl + 1 cross-file), got: {}",
        refs.len()
    );

    h.shutdown().await;
}

/// Find references across multiple importers.
#[tokio::test]
async fn cross_file_references_multiple_importers() {
    let mut h = LspTestHarness::new(&[
        (
            "lib.nix",
            indoc! {"
                { helper = x: x + 1; }
                # ^1
            "},
        ),
        ("a.nix", "let lib = import ./lib.nix; in lib.helper 42"),
        ("b.nix", "let l = import ./lib.nix; in l.helper 10"),
    ])
    .await;

    h.open("lib.nix").await;
    let _ = h.wait_for_diagnostics("lib.nix", TIMEOUT).await;
    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("lib.nix");
    let refs = h
        .references("lib.nix", m[&1].line, m[&1].character, true)
        .await
        .expect("references should return results");

    let a_uri = tower_lsp::lsp_types::Url::from_file_path(h.workspace.path("a.nix")).unwrap();
    let b_uri = tower_lsp::lsp_types::Url::from_file_path(h.workspace.path("b.nix")).unwrap();

    let has_a = refs.iter().any(|loc| loc.uri == a_uri);
    let has_b = refs.iter().any(|loc| loc.uri == b_uri);

    assert!(has_a, "expected a reference in a.nix, got: {refs:?}");
    assert!(has_b, "expected a reference in b.nix, got: {refs:?}");
    // 1 declaration + 2 cross-file usages = 3
    assert!(
        refs.len() >= 3,
        "expected at least 3 references, got: {}",
        refs.len()
    );

    h.shutdown().await;
}
