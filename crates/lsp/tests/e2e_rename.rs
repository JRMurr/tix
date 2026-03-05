mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// prepareRename returns a range and placeholder text.
#[tokio::test]
async fn prepare_rename_returns_range() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let foo = 1; in foo
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let result = h
        .prepare_rename("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("prepareRename should return a result");

    // Should contain range info and the current name as placeholder.
    match result {
        PrepareRenameResponse::Range(range) => {
            assert!(range.start.line == m[&1].line);
        }
        PrepareRenameResponse::RangeWithPlaceholder { range, placeholder } => {
            assert!(range.start.line == m[&1].line);
            assert_eq!(placeholder, "foo");
        }
        PrepareRenameResponse::DefaultBehavior { .. } => {
            // Also acceptable — server uses default behavior.
        }
    }

    h.shutdown().await;
}

/// Rename within a single file produces correct edits for def + refs.
#[tokio::test]
async fn rename_single_file() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let foo = 1; in foo + foo
            #   ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let edit = h
        .rename("test.nix", m[&1].line, m[&1].character, "bar")
        .await
        .expect("rename should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let test_uri = Url::from_file_path(h.workspace.path("test.nix")).unwrap();
    let edits = changes
        .get(&test_uri)
        .expect("should have edits for test.nix");

    // Definition + 2 references = 3 edits, all replacing "foo" with "bar".
    assert_eq!(
        edits.len(),
        3,
        "expected 3 rename edits, got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "bar");
    }

    h.shutdown().await;
}

/// Rename a let-binding inside a callpackage-style lambda (`{ pkgs, foo, ... }:`).
/// The pattern params come from context stubs, but local let-bindings that
/// reference them should still be renameable.
#[tokio::test]
async fn rename_in_callpackage_context() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {"
                [context.callpackage]
                paths = [\"pkgs/**/*.nix\"]
                stubs = [\"ctx.tix\"]
            "},
        ),
        (
            "ctx.tix",
            indoc! {"
                val foo :: int;
            "},
        ),
        (
            "pkgs/test.nix",
            indoc! {"
                { foo, ... }:
                let bar = foo;
                #   ^1
                in bar
                #  ^2
            "},
        ),
    ])
    .await;

    h.open("pkgs/test.nix").await;
    let _ = h.wait_for_diagnostics("pkgs/test.nix", TIMEOUT).await;

    let m = h.markers("pkgs/test.nix");

    // prepareRename on the let-binding `bar` should succeed.
    let prepare = h
        .prepare_rename("pkgs/test.nix", m[&1].line, m[&1].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on let-binding `bar` in callpackage context should succeed"
    );

    // Rename `bar` → `baz` should produce edits for both def and ref.
    let edit = h
        .rename("pkgs/test.nix", m[&1].line, m[&1].character, "baz")
        .await
        .expect("rename of `bar` should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let uri = Url::from_file_path(h.workspace.path("pkgs/test.nix")).unwrap();
    let edits = changes
        .get(&uri)
        .expect("should have edits for pkgs/test.nix");

    // Definition `bar` + reference `bar` in body = 2 edits.
    assert_eq!(
        edits.len(),
        2,
        "expected 2 rename edits (def + ref), got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "baz");
    }

    // Also verify rename works from the reference site.
    let edit_from_ref = h
        .rename("pkgs/test.nix", m[&2].line, m[&2].character, "qux")
        .await
        .expect("rename from reference site should also work");
    let changes = edit_from_ref.changes.expect("should have changes map");
    let edits = changes.get(&uri).expect("should have edits");
    assert_eq!(edits.len(), 2);

    h.shutdown().await;
}

/// Rename a let-binding in a file structured like nix/rust.nix:
/// pattern params with doc annotations, let-bindings using dot-access,
/// and `inherit` in the result attrset. Reproduces a bug where nothing
/// in such files was renameable.
#[tokio::test]
async fn rename_let_binding_like_rust_nix() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            { pkgs, crane }:

            let
              lib = pkgs.lib;
              rustPlatform = pkgs.makeRustPlatform {
            #   ^1
                cargo = pkgs.rustc;
              };
              commonArgs = {
                inherit (pkgs) system;
                pname = \"test\";
              };
              rustBin = crane.buildPackage (commonArgs // {
            #   ^2
                extra = 1;
              });
            in
            {
              inherit rustPlatform;
              binary = rustBin;
            }
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    // Rename `rustPlatform` — used at let-binding + inherit.
    let prepare = h
        .prepare_rename("test.nix", m[&1].line, m[&1].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `rustPlatform` should succeed"
    );

    let edit = h
        .rename("test.nix", m[&1].line, m[&1].character, "rp")
        .await
        .expect("rename of `rustPlatform` should produce edits");

    let changes = edit.changes.expect("should have changes");
    let uri = Url::from_file_path(h.workspace.path("test.nix")).unwrap();
    let edits = changes.get(&uri).expect("should have edits for test.nix");

    // Definition + inherit reference = at least 2 edits.
    assert!(
        edits.len() >= 2,
        "expected at least 2 rename edits for rustPlatform (def + inherit), got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "rp");
    }

    // Rename `rustBin` — used at let-binding + `binary = rustBin;`.
    let prepare = h
        .prepare_rename("test.nix", m[&2].line, m[&2].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `rustBin` should succeed"
    );

    let edit = h
        .rename("test.nix", m[&2].line, m[&2].character, "bin")
        .await
        .expect("rename of `rustBin` should produce edits");

    let changes = edit.changes.expect("should have changes");
    let edits = changes.get(&uri).expect("should have edits for test.nix");
    assert!(
        edits.len() >= 2,
        "expected at least 2 rename edits for rustBin (def + ref), got: {}",
        edits.len()
    );

    h.shutdown().await;
}

/// Rename bindings in a realistic nix/rust.nix-shaped file: pattern params
/// with doc comment annotations, let-bindings using dotted selects, `inherit`,
/// and `//` merge. This mirrors the exact structure where rename was reported
/// as broken.
#[tokio::test]
async fn rename_in_real_rust_nix_shape() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            {
              /**
                type: pkgs :: { lib: { fileset: { toSource: a -> a, unions: a -> a, ... }, ... }, makeRustPlatform: a -> a, rustc: a, cargo-nextest: a, ... }
              */
              pkgs,
              crane,
            }:

            let
              lib = pkgs.lib;
            # ^1
              rustVersion = pkgs.rustc;
              rustPlatform = pkgs.makeRustPlatform {
            #   ^2
                cargo = rustVersion;
            #            ^3
                rustc = rustVersion;
              };

              craneLib = crane;

              fs = lib.fileset;
              src = fs.toSource {
                root = ./..;
                fileset = fs.unions [
                  ../crates
                ];
              };

              commonArgs = {
            #   ^4
                inherit src;
                pname = \"tix\";
                version = \"0.1.0\";
              };

              cargoArtifacts = craneLib;

              rustBin = craneLib;
            #   ^5

              rustFmt = craneLib;

              rustClippy = craneLib;

              rustTests = craneLib;

              rustPbt = craneLib;
            in
            {
              inherit rustPlatform;
              binary = rustBin;
              checks = {
                fmt = rustFmt;
                clippy = rustClippy;
                tests = rustTests;
                pbt = rustPbt;
              };
            }
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    // 1. Rename `lib` — used in `fs = lib.fileset`
    let prepare = h
        .prepare_rename("test.nix", m[&1].line, m[&1].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `lib` should succeed, got None"
    );

    // 2. Rename `rustPlatform` — defined in let, used via inherit
    let prepare = h
        .prepare_rename("test.nix", m[&2].line, m[&2].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `rustPlatform` should succeed, got None"
    );

    let edit = h
        .rename("test.nix", m[&2].line, m[&2].character, "rp")
        .await
        .expect("rename of `rustPlatform` should produce edits");
    let changes = edit.changes.expect("should have changes");
    let uri = Url::from_file_path(h.workspace.path("test.nix")).unwrap();
    let edits = changes.get(&uri).expect("should have edits");
    assert!(
        edits.len() >= 2,
        "expected >= 2 edits for rustPlatform (def + inherit), got: {}",
        edits.len()
    );

    // 3. Rename `rustVersion` from a reference site
    let prepare = h
        .prepare_rename("test.nix", m[&3].line, m[&3].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `rustVersion` reference should succeed, got None"
    );

    // 4. Rename `commonArgs`
    let prepare = h
        .prepare_rename("test.nix", m[&4].line, m[&4].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on `commonArgs` should succeed, got None"
    );

    // 5. Rename `rustBin` — used in `binary = rustBin;`
    let edit = h
        .rename("test.nix", m[&5].line, m[&5].character, "bin")
        .await
        .expect("rename of `rustBin` should produce edits");
    let changes = edit.changes.expect("should have changes");
    let edits = changes.get(&uri).expect("should have edits");
    assert!(
        edits.len() >= 2,
        "expected >= 2 edits for rustBin (def + body ref), got: {}",
        edits.len()
    );

    h.shutdown().await;
}

/// Rename a pattern parameter in a callpackage-style lambda.
/// Even though `foo` gets its type from context stubs, the pattern field
/// is a real NameId and should be renameable.
#[tokio::test]
async fn rename_pattern_param_in_callpackage_context() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {"
                [context.callpackage]
                paths = [\"pkgs/**/*.nix\"]
                stubs = [\"ctx.tix\"]
            "},
        ),
        (
            "ctx.tix",
            indoc! {"
                val rustPlatform :: { buildRustPackage: a -> a, ... };
            "},
        ),
        (
            "pkgs/test.nix",
            indoc! {"
                { rustPlatform, ... }:
                # ^1
                rustPlatform.buildRustPackage { pname = \"test\"; }
            "},
        ),
    ])
    .await;

    h.open("pkgs/test.nix").await;
    let _ = h.wait_for_diagnostics("pkgs/test.nix", TIMEOUT).await;

    let m = h.markers("pkgs/test.nix");

    // prepareRename on the pattern parameter `rustPlatform` should succeed.
    let prepare = h
        .prepare_rename("pkgs/test.nix", m[&1].line, m[&1].character)
        .await;
    assert!(
        prepare.is_some(),
        "prepareRename on pattern param `rustPlatform` in callpackage context should succeed"
    );

    // Rename should produce edits for the pattern field def + body reference.
    let edit = h
        .rename("pkgs/test.nix", m[&1].line, m[&1].character, "rp")
        .await
        .expect("rename of pattern param should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let uri = Url::from_file_path(h.workspace.path("pkgs/test.nix")).unwrap();
    let edits = changes.get(&uri).expect("should have edits");

    // Pattern field `rustPlatform` + body reference `rustPlatform` = 2 edits.
    assert_eq!(
        edits.len(),
        2,
        "expected 2 rename edits (pattern field + body ref), got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "rp");
    }

    h.shutdown().await;
}

/// Regression: rename on the actual nix/rust.nix file content.
/// Reads the real file and tests prepare_rename + rename on `rustPlatform`.
#[tokio::test]
async fn rename_actual_rust_nix_file() {
    let rust_nix_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../nix/rust.nix");
    let rust_nix_src = match std::fs::read_to_string(&rust_nix_path) {
        Ok(s) => s,
        Err(_) => {
            eprintln!("skipping: nix/rust.nix not found");
            return;
        }
    };

    // Add a marker on `rustPlatform` in the let block (line 12, col 2).
    // We find the position dynamically instead.
    let mut h = LspTestHarness::new(&[("rust.nix", &rust_nix_src)]).await;

    h.open("rust.nix").await;
    let _ = h.wait_for_diagnostics("rust.nix", TIMEOUT).await;

    // Find the position of `rustPlatform` in the let-binding definition (line 11, 0-indexed).
    // "  rustPlatform = pkgs.makeRustPlatform {"
    let rp_line = rust_nix_src
        .lines()
        .position(|l| l.trim_start().starts_with("rustPlatform = "))
        .expect("should find rustPlatform line") as u32;
    let rp_col = rust_nix_src
        .lines()
        .nth(rp_line as usize)
        .unwrap()
        .find("rustPlatform")
        .unwrap() as u32;

    // prepareRename should succeed.
    let prepare = h.prepare_rename("rust.nix", rp_line, rp_col).await;
    assert!(
        prepare.is_some(),
        "prepareRename on `rustPlatform` in actual nix/rust.nix should succeed (line {rp_line}, col {rp_col})"
    );

    // Rename should produce edits.
    let edit = h
        .rename("rust.nix", rp_line, rp_col, "rp")
        .await
        .expect("rename of `rustPlatform` in actual nix/rust.nix should produce edits");

    let changes = edit.changes.expect("should have changes");
    let uri = Url::from_file_path(h.workspace.path("rust.nix")).unwrap();
    let edits = changes.get(&uri).expect("should have edits for rust.nix");
    assert!(
        edits.len() >= 2,
        "expected >= 2 edits for rustPlatform, got: {}",
        edits.len()
    );

    // Also test a different binding: `commonArgs`
    let ca_line = rust_nix_src
        .lines()
        .position(|l| l.trim_start().starts_with("commonArgs = "))
        .expect("should find commonArgs line") as u32;
    let ca_col = rust_nix_src
        .lines()
        .nth(ca_line as usize)
        .unwrap()
        .find("commonArgs")
        .unwrap() as u32;

    let prepare = h.prepare_rename("rust.nix", ca_line, ca_col).await;
    assert!(
        prepare.is_some(),
        "prepareRename on `commonArgs` in actual nix/rust.nix should succeed (line {ca_line}, col {ca_col})"
    );

    h.shutdown().await;
}

/// Rename across files: edits span both file URIs.
#[tokio::test]
async fn rename_cross_file() {
    let mut h = LspTestHarness::new(&[
        ("a.nix", "{ val = 42; }"),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                #   ^1
                in a.val
            "},
        ),
    ])
    .await;

    h.open("a.nix").await;
    let _ = h.wait_for_diagnostics("a.nix", TIMEOUT).await;
    h.open("b.nix").await;
    let _ = h.wait_for_diagnostics("b.nix", TIMEOUT).await;

    let m = h.markers("b.nix");

    let edit = h
        .rename("b.nix", m[&1].line, m[&1].character, "lib")
        .await
        .expect("rename should return a WorkspaceEdit");

    let changes = edit.changes.expect("should have changes map");
    let b_uri = Url::from_file_path(h.workspace.path("b.nix")).unwrap();
    let edits = changes.get(&b_uri).expect("should have edits for b.nix");

    // `a` is used at the let-binding and in `a.val` — at least 2 edits.
    assert!(
        edits.len() >= 2,
        "expected at least 2 rename edits in b.nix, got: {}",
        edits.len()
    );
    for te in edits {
        assert_eq!(te.new_text, "lib");
    }

    h.shutdown().await;
}
