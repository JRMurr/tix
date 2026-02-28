mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Hover after analysis shows the binding's type.
#[tokio::test]
async fn hover_shows_type_after_analysis() {
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

    // Hover on the binding site should show the type.
    let hover = h
        .hover("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover should return a result");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover should contain 'int', got: {}",
        content.value,
    );

    // Hover on the reference should also show the type.
    let hover = h
        .hover("test.nix", m[&2].line, m[&2].character)
        .await
        .expect("hover on reference should return a result");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(
        content.value.contains("int"),
        "hover on reference should contain 'int', got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Hover updates after editing the file.
#[tokio::test]
async fn hover_updates_after_edit() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let hover = h
        .hover("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("initial hover");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(content.value.contains("int"));

    // Edit: change from int to string.
    h.edit(
        "test.nix",
        indoc! {"
            let x = \"hello\"; in x
            #   ^1
        "},
    )
    .await;

    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let hover = h
        .hover("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover after edit");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(
        content.value.contains("string"),
        "hover should show 'string' after edit, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Hover on an attrset field shows the field type.
#[tokio::test]
async fn hover_on_attrset_field() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let r = { name = \"foo\"; age = 42; };
            in r.name
            #    ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let hover = h
        .hover("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on field access");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(
        content.value.contains("string"),
        "field access hover should show 'string', got: {}",
        content.value,
    );

    h.shutdown().await;
}
