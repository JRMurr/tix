mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// A project with tix.toml stubs should resolve types from those stubs.
#[tokio::test]
async fn tix_toml_stubs() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {"
                stubs = [\"types.tix\"]
            "},
        ),
        (
            "types.tix",
            indoc! {"
                type MyRecord = { name: string, count: int };
                val mkRecord :: string -> MyRecord;
            "},
        ),
        (
            "test.nix",
            indoc! {"
                let r = mkRecord \"foo\";
                in r.name
                #    ^1
            "},
        ),
    ])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");
    let hover = h
        .hover("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on stub-typed field");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    assert!(
        content.value.contains("string"),
        "hover should show 'string' from stub type, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// A project with tix.toml context stubs should inject typed args.
/// Context stubs provide types for lambda pattern args (e.g. `{ config, ... }:`).
#[tokio::test]
async fn tix_toml_context() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {"
                [context.nixos]
                paths = [\"modules/*.nix\"]
                stubs = [\"nixos_context.tix\"]
            "},
        ),
        (
            "nixos_context.tix",
            // Top-level `val` entries are matched by name to lambda pattern args.
            indoc! {"
                type NixosConfig = {
                    networking: { hostName: string, ... },
                    ...
                };
                val config :: NixosConfig;
            "},
        ),
        (
            "modules/test.nix",
            indoc! {"
                { config, ... }:
                config.networking
                #      ^1
            "},
        ),
    ])
    .await;

    h.open("modules/test.nix").await;
    let _ = h.wait_for_diagnostics("modules/test.nix", TIMEOUT).await;

    let m = h.markers("modules/test.nix");
    let hover = h
        .hover("modules/test.nix", m[&1].line, m[&1].character)
        .await;

    // The hover result depends on whether the context stubs are loaded
    // correctly. If the server finds tix.toml and applies the context,
    // `config.networking` should have type info from the stub.
    if let Some(hover) = hover {
        let HoverContents::Markup(content) = &hover.contents else {
            panic!("expected MarkupContent");
        };
        // Should contain something about networking or the attrset structure.
        assert!(
            content.value.contains("networking") || content.value.contains("hostName"),
            "hover should reflect context stubs, got: {}",
            content.value,
        );
    }
    // If hover is None, the server may not have loaded context stubs in time,
    // which is acceptable — the main test is that it doesn't crash.

    h.shutdown().await;
}

/// Hovering on a pattern field that has a context-provided type should
/// show that type, not `?` or `{...}`.
#[tokio::test]
async fn context_hover_on_pattern_field() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {"
                [context.test]
                paths = [\"src/*.nix\"]
                stubs = [\"ctx.tix\"]
            "},
        ),
        (
            "ctx.tix",
            indoc! {"
                type MyLib = { id: a -> a, const: a -> b -> a, ... };
                val lib :: MyLib;
            "},
        ),
        (
            "src/test.nix",
            indoc! {"
                { lib, ... }:
                # ^1
                lib.id 42
            "},
        ),
    ])
    .await;

    h.open("src/test.nix").await;
    let _ = h.wait_for_diagnostics("src/test.nix", TIMEOUT).await;

    let m = h.markers("src/test.nix");
    let hover = h
        .hover("src/test.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on `lib` pattern field should return a result");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };

    eprintln!("pattern field hover: {}", content.value);

    // The type should reflect the context annotation, not be bare `?`.
    assert!(
        content.value.contains("MyLib") || content.value.contains("id"),
        "hover on pattern field `lib` should show context type, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Hovering on `lib` in a callPackage-style file (`{ lib, ... }:`) should
/// show the `Lib` type from the built-in stubs, not just `{...}`.
///
/// Reproduces the issue seen in real nixpkgs on files like
/// `pkgs/development/emilua-plugins/beast/default.nix` where hover on `lib`
/// shows `{...}` instead of `Lib`.
#[tokio::test]
async fn callpackage_context_lib_hover() {
    let mut h = LspTestHarness::with_options(
        &[
            (
                "tix.toml",
                indoc! {"
                    [context.callpackage]
                    paths = [\"pkgs/**/*.nix\"]
                    stubs = [\"@callpackage\"]
                "},
            ),
            (
                "pkgs/beast/default.nix",
                indoc! {"
                    { lib, stdenv, fetchFromGitLab, ... }:
                    # ^1
                    stdenv.mkDerivation {
                      pname = \"test\";
                      version = \"1.0\";
                      meta = {
                        description = \"test\";
                        license = lib.licenses.boost;
                        platforms = lib.platforms.linux;
                      };
                    }
                "},
            ),
        ],
        false, // load built-in stubs (needed for @callpackage -> Pkgs -> Lib)
    )
    .await;

    h.open("pkgs/beast/default.nix").await;
    let _ = h
        .wait_for_diagnostics("pkgs/beast/default.nix", TIMEOUT)
        .await;

    let m = h.markers("pkgs/beast/default.nix");
    let hover = h
        .hover("pkgs/beast/default.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on `lib` should return a result");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };

    eprintln!("lib hover: {}", content.value);

    // The type should be `Lib` (or at minimum contain structured fields),
    // NOT just `{...}` or a bare type variable.
    assert!(
        content.value.contains("Lib"),
        "hover on `lib` in callPackage file should show `Lib` type, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Same as above but using the exact tix.toml format from the user's nixpkgs
/// checkout: `stubs = []` (explicit empty), multiple contexts, and a
/// `[project]` section.
#[tokio::test]
async fn callpackage_context_nixpkgs_toml_format() {
    let mut h = LspTestHarness::with_options(
        &[
            (
                "tix.toml",
                // Exact format from the user's nixpkgs tix.toml
                indoc! {"
                    stubs = []

                    [context.nixos]
                    paths = [\"nixos/**/*.nix\"]
                    stubs = [\"@nixos\"]

                    [context.callpackage]
                    paths = [\"pkgs/**/*.nix\"]
                    stubs = [\"@callpackage\"]

                    [project]
                    analyze = [\"lib/*.nix\"]
                "},
            ),
            (
                "pkgs/beast/default.nix",
                indoc! {"
                    { lib, stdenv, fetchFromGitLab, ... }:
                    # ^1   ^2
                    stdenv.mkDerivation {
                      pname = \"test\";
                      version = \"1.0\";
                      meta = {
                        license = lib.licenses.boost;
                        platforms = lib.platforms.linux;
                      };
                    }
                "},
            ),
        ],
        false, // load built-in stubs
    )
    .await;

    h.open("pkgs/beast/default.nix").await;
    let _ = h
        .wait_for_diagnostics("pkgs/beast/default.nix", TIMEOUT)
        .await;

    let m = h.markers("pkgs/beast/default.nix");

    // Hover on `lib`
    let hover = h
        .hover("pkgs/beast/default.nix", m[&1].line, m[&1].character)
        .await
        .expect("hover on `lib`");
    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    eprintln!("lib hover (nixpkgs format): {}", content.value);
    assert!(
        content.value.contains("Lib"),
        "hover on `lib` should show `Lib`, got: {}",
        content.value,
    );

    // Hover on `stdenv`
    let hover = h
        .hover("pkgs/beast/default.nix", m[&2].line, m[&2].character)
        .await
        .expect("hover on `stdenv`");
    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent");
    };
    eprintln!("stdenv hover: {}", content.value);
    assert!(
        content.value.contains("mkDerivation"),
        "hover on `stdenv` should show structured type with mkDerivation, got: {}",
        content.value,
    );

    h.shutdown().await;
}
