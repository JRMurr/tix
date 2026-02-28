mod common;

use common::TIMEOUT;

#[tokio::test]
async fn initialize_open_close() {
    let mut h = common::LspTestHarness::new(&[("test.nix", "let x = 1; in x")]).await;

    h.open("test.nix").await;
    let diags = h.wait_for_diagnostics("test.nix", TIMEOUT).await;
    assert!(diags.is_some(), "should receive diagnostics after open");

    h.close("test.nix").await;
    h.shutdown().await;
}

#[tokio::test]
async fn open_same_file_twice_no_crash() {
    let mut h = common::LspTestHarness::new(&[("test.nix", "let x = 1; in x")]).await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    // Opening the same file again should not crash.
    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    h.shutdown().await;
}
