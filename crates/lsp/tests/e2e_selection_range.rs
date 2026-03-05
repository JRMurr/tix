mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;

/// Selection range returns a linked-list parent chain.
#[tokio::test]
async fn selection_range_nesting() {
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

    let ranges = h
        .selection_range("test.nix", &[m[&1]])
        .await
        .expect("selection_range should return results");

    assert_eq!(ranges.len(), 1, "should return one range per position");

    // The innermost range should have a parent (expanding outward).
    let range = &ranges[0];
    assert!(
        range.parent.is_some(),
        "selection range should have a parent (wider enclosing range)"
    );

    // Walk the parent chain — it should eventually end (no infinite loop).
    let mut depth = 0;
    let mut current = range.parent.as_ref();
    while let Some(parent) = current {
        depth += 1;
        current = parent.parent.as_ref();
        assert!(depth < 100, "parent chain should be finite");
    }
    assert!(depth >= 1, "should have at least one parent level");

    h.shutdown().await;
}

/// Multiple positions in one request return multiple selection ranges.
#[tokio::test]
async fn selection_range_multiple_positions() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 1; y = 2; in x + y
            #   ^1     ^2
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let ranges = h
        .selection_range("test.nix", &[m[&1], m[&2]])
        .await
        .expect("selection_range should return results");

    assert_eq!(
        ranges.len(),
        2,
        "should return exactly 2 selection ranges for 2 positions"
    );

    h.shutdown().await;
}
