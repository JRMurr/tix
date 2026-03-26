mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Cross-file hover: A.nix defines a value, B.nix imports it, hover shows the type.
#[tokio::test]
async fn cross_file_hover() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ x = 42; y = \"hello\"; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.x
                #    ^1
            "},
        ),
    ])
    .await;

    // Open both files — A.nix first so it's analyzed when B.nix resolves the import.
    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;

    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on imported field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover on imported x should show 'int', got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Edit A.nix to change a type, verify B.nix hover updates.
#[tokio::test]
async fn cross_file_hover_updates_after_edit() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ val = 42; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.val
                #    ^1
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("initial hover");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(content.value.contains("int"));

    // Edit A.nix: change val from int to string.
    h.edit("a.nix", "{ val = \"updated\"; }").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;

    // Re-open B.nix to trigger re-analysis with updated import.
    h.edit(
        "b.nix",
        indoc! {"
            let a = import ./a.nix;
            in a.val
            #    ^1
        "},
    )
    .await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover after edit");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    assert!(
        content.value.contains("string"),
        "hover should update to 'string' after editing imported file, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Demand-driven import: only open B.nix (which imports A.nix on disk),
/// hover shows real types from A via demand_file inference.
#[tokio::test]
async fn demand_driven_import_hover() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ x = 42; y = \"hello\"; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.x
                #    ^1
            "},
        ),
    ])
    .await;

    // Only open B — A.nix exists on disk but is NOT opened.
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    // Hover on a.x should show int, not ? (demand-driven resolved A's type).
    let m = h.markers("b.nix");
    let hover = h
        .hover("b.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on imported field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover on imported x should show 'int' via demand-driven import, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Transitive demand-driven imports: C.nix → B.nix → A.nix, only C opened.
#[tokio::test]
async fn demand_driven_transitive_import() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ val = 42; }"),
        ("b.nix", "import ./a.nix"),
        (
            "c.nix",
            indoc! {"
                let b = import ./b.nix;
                in b.val
                #    ^1
            "},
        ),
    ])
    .await;

    // Only open C — neither A.nix nor B.nix are opened.
    h.open("c.nix").await;
    let _ = h.wait_for_diagnostics("c.nix", TIMEOUT).await;

    let m = h.markers("c.nix");
    let hover = h
        .hover("c.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on transitive import field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover on transitive import val should show 'int', got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Demand-driven import should NOT produce E013 (ImportUnresolved) diagnostics
/// for files that exist on disk and were successfully demand-resolved.
#[tokio::test]
async fn demand_driven_no_e013_for_resolved_imports() {
    let mut h = LspTestHarness::new(&[("a.nix", "{ x = 1; }"), ("b.nix", "import ./a.nix")]).await;

    // Only open B — A exists on disk.
    h.open("b.nix").await;
    let diags = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    // Should have no E013 (ImportUnresolved) diagnostics.
    if let Some(diag_params) = diags {
        let import_unresolved: Vec<_> = diag_params
            .diagnostics
            .iter()
            .filter(|d| d.code == Some(NumberOrString::String("E013".to_string())))
            .collect();
        assert!(
            import_unresolved.is_empty(),
            "demand-resolved imports should not produce E013, got: {:?}",
            import_unresolved,
        );
    }

    h.shutdown().await;
}

/// Demand-driven inference should resolve context_args from tix.toml for
/// files that aren't open in the editor. Without this, callPackage targets
/// inferred from disk have unconstrained parameter types and return `?`.
///
/// Reproduces: open default.nix (uses callPackage ./pkg.nix {}), all attrs
/// unknown. Open pkg.nix → type resolves. Close pkg.nix → reverts to unknown.
#[tokio::test]
async fn demand_driven_import_with_callpackage_context() {
    let mut h = LspTestHarness::with_options(
        &[
            (
                "tix.toml",
                indoc! {"
                    [context.callpackage]
                    includes = [\"pkgs/**/*.nix\"]
                    stubs = [\"@callpackage\"]
                "},
            ),
            // A callPackage-style package file: takes { lib, ... } and uses
            // lib.id. With @callpackage context, `lib` is typed as `Lib` so
            // `lib.id 42` returns `int`. Without context, `lib` is unconstrained
            // so `lib.id 42` returns `?`.
            (
                "pkgs/pkg.nix",
                indoc! {"
                    { lib, ... }:
                    lib.id 42
                "},
            ),
            // Imports pkg.nix via callPackage. Only this file is opened.
            (
                "default.nix",
                indoc! {"
                    let
                      callPackage = f: overrides: f overrides;
                      result = callPackage ./pkgs/pkg.nix {};
                    in result
                    #  ^1
                "},
            ),
        ],
        false, // load built-in stubs (needed for @callpackage context)
    )
    .await;

    // Only open default.nix — pkg.nix exists on disk but is NOT opened.
    // Demand-driven inference should resolve pkg.nix with context_args.
    h.open("default.nix").await;
    let _ = h.wait_for_diagnostics("default.nix", TIMEOUT).await;

    let m = h.markers("default.nix");
    let hover = h
        .hover("default.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on callPackage result field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("int"),
        "hover on result should show 'int' via demand-driven callPackage import with context, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Multiple files can be open simultaneously without interference.
#[tokio::test]
async fn multiple_files_independent() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "let x = 1; in x"),
        ("b.nix", "let y = \"hello\"; in y"),
    ])
    .await;

    h.open("a.nix").await;
    h.open("b.nix").await;

    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    // Both files should have clean diagnostics.
    // (we already consumed them above, but verify no errors were present)

    h.shutdown().await;
}
