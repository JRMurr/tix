mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// Workspace symbols returns symbols from both open files.
#[tokio::test]
async fn symbols_across_files() {
    let mut h = LspTestHarness::new(&[
        (
            "a.nix",
            indoc! {"
                let alpha = 1; in alpha
            "},
        ),
        (
            "b.nix",
            indoc! {"
                let beta = 2; in beta
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let symbols = h
        .workspace_symbols("")
        .await
        .expect("workspace_symbols should return results");

    let names: Vec<&str> = symbols.iter().map(|s| s.name.as_str()).collect();
    assert!(
        names.iter().any(|n| n.contains("alpha")),
        "should contain 'alpha' from a.nix, got: {names:?}"
    );
    assert!(
        names.iter().any(|n| n.contains("beta")),
        "should contain 'beta' from b.nix, got: {names:?}"
    );

    h.shutdown().await;
}

/// Workspace symbols query string filters results.
#[tokio::test]
async fn symbols_query_filter() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let
              fooBar = 1;
              bazQux = 2;
            in fooBar + bazQux
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let symbols = h
        .workspace_symbols("foo")
        .await
        .expect("workspace_symbols should return results");

    let names: Vec<&str> = symbols.iter().map(|s| s.name.as_str()).collect();
    assert!(
        names.iter().any(|n| n.contains("fooBar")),
        "query 'foo' should match 'fooBar', got: {names:?}"
    );

    // "bazQux" should be filtered out by the query.
    assert!(
        !names.iter().any(|n| n.contains("bazQux")),
        "query 'foo' should not match 'bazQux', got: {names:?}"
    );

    h.shutdown().await;
}
