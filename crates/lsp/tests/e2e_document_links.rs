mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// An `import ./a.nix` expression produces a DocumentLink with a target URI.
#[tokio::test]
async fn import_produces_link() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "42"),
        (
            "b.nix",
            indoc! {"
                import ./a.nix
            "},
        ),
    ])
    .await;

    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let links = h
        .document_links("b.nix")
        .await
        .expect("document_links should return results");

    assert!(
        !links.is_empty(),
        "import expression should produce at least one DocumentLink"
    );

    // The link target should point to a.nix.
    let a_path = h.workspace.path("a.nix");
    let has_a_target = links.iter().any(|link| {
        link.target
            .as_ref()
            .map(|uri| uri.to_file_path().ok() == Some(a_path.clone()))
            .unwrap_or(false)
    });

    assert!(
        has_a_target,
        "one of the document links should target a.nix, got: {:?}",
        links.iter().map(|l| &l.target).collect::<Vec<_>>()
    );

    h.shutdown().await;
}
