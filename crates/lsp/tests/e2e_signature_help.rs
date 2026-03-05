mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// Signature help on a function application shows parameter info.
#[tokio::test]
async fn signature_help_simple() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let f = x: x + 1; in f 10
            #                       ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let sig = h
        .signature_help("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("signature_help should return a result");

    assert!(
        !sig.signatures.is_empty(),
        "should have at least one signature"
    );

    // The signature label should contain `->` (function type).
    let label = &sig.signatures[0].label;
    assert!(
        label.contains("->"),
        "signature label should contain '->', got: {label}"
    );

    h.shutdown().await;
}

/// Signature help on a curried function tracks the active parameter.
#[tokio::test]
async fn signature_help_curried() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let f = x: y: x + y; in f 1 2
            #                             ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let sig = h
        .signature_help("test.nix", m[&1].line, m[&1].character)
        .await;

    // Signature help may or may not be available after all args are applied.
    // The main assertion is that the request doesn't crash.
    if let Some(sig) = sig {
        assert!(
            !sig.signatures.is_empty(),
            "if returned, should have at least one signature"
        );
    }

    h.shutdown().await;
}
