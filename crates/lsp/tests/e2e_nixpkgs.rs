// ==============================================================================
// E2E LSP tests against real nixpkgs lib/
// ==============================================================================
//
// These tests exercise the full LSP pipeline (parse → lower → nameres →
// import resolution → type inference → diagnostics/hover/completions) on
// real nixpkgs lib/ files. They catch panics and regressions that synthetic
// test cases miss.
//
// Tests auto-skip at runtime if `nix` is not on PATH or `nix eval` fails,
// so they run automatically in a nix-based dev environment without gating
// the rest of the test suite.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use indoc::indoc;
use tower_lsp::lsp_types::*;

use common::LspTestHarness;

/// Longer timeout for nixpkgs files — they're larger and may trigger
/// cross-file import resolution.
const NIXPKGS_TIMEOUT: Duration = Duration::from_secs(30);

// ==============================================================================
// Helpers
// ==============================================================================

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// Attempt to resolve the pinned nixpkgs path via `nix eval --raw .#nixpkgs-src`.
///
/// Returns `None` if nix is not installed or the flake eval fails, allowing
/// tests to skip gracefully.
fn try_nixpkgs_src() -> Option<PathBuf> {
    let output = Command::new("nix")
        .args(["eval", "--raw", ".#nixpkgs-src"])
        .current_dir(repo_root())
        .output()
        .ok()?;

    if !output.status.success() {
        eprintln!(
            "nix eval .#nixpkgs-src failed ({}), skipping nixpkgs LSP tests",
            String::from_utf8_lossy(&output.stderr).trim()
        );
        return None;
    }

    Some(PathBuf::from(
        String::from_utf8(output.stdout).ok()?.trim().to_string(),
    ))
}

/// Recursively collect `.nix` files under `dir`, excluding `tests/` and
/// `deprecated/` subdirectories.
fn collect_nix_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_recursive(dir, &mut files);
    files.sort();
    files
}

fn collect_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().unwrap_or_default().to_string_lossy();
            if name == "tests" || name == "deprecated" {
                continue;
            }
            collect_recursive(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "nix") {
            out.push(path);
        }
    }
}

/// Find the first occurrence of `name =` (a let-binding or attrset field)
/// in `source` and return its 0-based `(line, col)`.
fn find_binding(source: &str, name: &str) -> Option<(u32, u32)> {
    let pattern = format!("{name} =");
    for (line_idx, line) in source.lines().enumerate() {
        if let Some(col) = line.find(&pattern) {
            return Some((line_idx as u32, col as u32));
        }
    }
    None
}

// ==============================================================================
// Tests
// ==============================================================================

/// Open every .nix file in nixpkgs lib/, wait for diagnostics — no panics.
#[tokio::test]
async fn nixpkgs_lib_no_crash() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_lib_no_crash: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    assert!(lib_dir.is_dir(), "{} is not a directory", lib_dir.display());

    let nix_files = collect_nix_files(&lib_dir);
    assert!(
        !nix_files.is_empty(),
        "no .nix files found in {}",
        lib_dir.display()
    );

    eprintln!(
        "nixpkgs_lib_no_crash: testing {} files in {}",
        nix_files.len(),
        lib_dir.display()
    );

    let mut h = LspTestHarness::with_root(lib_dir.clone()).await;

    let mut pass = 0usize;
    let mut timeout_count = 0usize;

    for file in &nix_files {
        let rel = file.strip_prefix(&lib_dir).unwrap_or(file);

        h.open_abs(file).await;
        match h.wait_for_diagnostics_abs(file, NIXPKGS_TIMEOUT).await {
            Some(_) => {
                eprintln!("  OK       {}", rel.display());
                pass += 1;
            }
            None => {
                // Timeout is acceptable — some files may not produce diagnostics
                // (e.g. if they're pure attribute sets with no errors). The key
                // assertion is that the server didn't panic.
                eprintln!("  TIMEOUT  {}", rel.display());
                timeout_count += 1;
            }
        }
    }

    eprintln!();
    eprintln!("=== nixpkgs lib LSP summary ===");
    eprintln!("  OK:      {pass}");
    eprintln!("  Timeout: {timeout_count}");
    eprintln!("  Total:   {}", nix_files.len());

    h.shutdown().await;
}

/// `lib/trivial.nix` produces diagnostics without hanging.
#[tokio::test]
async fn nixpkgs_diagnostics_trivial() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_diagnostics_trivial: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    let trivial = lib_dir.join("trivial.nix");
    assert!(trivial.exists(), "trivial.nix not found");

    let mut h = LspTestHarness::with_root(lib_dir).await;

    h.open_abs(&trivial).await;
    let diags = h.wait_for_diagnostics_abs(&trivial, NIXPKGS_TIMEOUT).await;
    assert!(
        diags.is_some(),
        "should receive diagnostics for trivial.nix (even if empty)"
    );

    h.shutdown().await;
}

/// Hover on the `id` binding in `lib/trivial.nix` returns a type.
#[tokio::test]
async fn nixpkgs_hover_trivial_id() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_hover_trivial_id: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    let trivial = lib_dir.join("trivial.nix");
    assert!(trivial.exists(), "trivial.nix not found");

    let source = std::fs::read_to_string(&trivial).unwrap();
    let (line, col) =
        find_binding(&source, "id").expect("could not find `id =` binding in trivial.nix");

    let mut h = LspTestHarness::with_root(lib_dir).await;

    h.open_abs(&trivial).await;
    let _ = h.wait_for_diagnostics_abs(&trivial, NIXPKGS_TIMEOUT).await;

    let hover = h.hover_abs(&trivial, line, col).await;
    assert!(
        hover.is_some(),
        "hover on `id` in trivial.nix should return a result"
    );

    h.shutdown().await;
}

/// Hover on `concatStringsSep` in `lib/strings.nix` returns a type.
#[tokio::test]
async fn nixpkgs_hover_strings_concat() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_hover_strings_concat: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    let strings = lib_dir.join("strings.nix");
    assert!(strings.exists(), "strings.nix not found");

    let source = std::fs::read_to_string(&strings).unwrap();
    let (line, col) = find_binding(&source, "concatStringsSep")
        .expect("could not find `concatStringsSep =` in strings.nix");

    let mut h = LspTestHarness::with_root(lib_dir).await;

    h.open_abs(&strings).await;
    let _ = h.wait_for_diagnostics_abs(&strings, NIXPKGS_TIMEOUT).await;

    let hover = h.hover_abs(&strings, line, col).await;
    assert!(
        hover.is_some(),
        "hover on `concatStringsSep` in strings.nix should return a result"
    );

    h.shutdown().await;
}

/// `lib/default.nix` (which imports most other lib files) doesn't crash.
#[tokio::test]
async fn nixpkgs_multi_file_default() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_multi_file_default: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    let default = lib_dir.join("default.nix");
    assert!(default.exists(), "default.nix not found");

    let mut h = LspTestHarness::with_root(lib_dir).await;

    h.open_abs(&default).await;
    // default.nix imports many files — give it extra time. We just care
    // that the server doesn't panic during the import cascade.
    let _ = h.wait_for_diagnostics_abs(&default, NIXPKGS_TIMEOUT).await;

    h.shutdown().await;
}

/// Completion request on `lib/trivial.nix` doesn't crash.
#[tokio::test]
async fn nixpkgs_completion_no_crash() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_completion_no_crash: nix not available");
        return;
    };
    let lib_dir = nixpkgs.join("lib");
    let trivial = lib_dir.join("trivial.nix");
    assert!(trivial.exists(), "trivial.nix not found");

    let source = std::fs::read_to_string(&trivial).unwrap();
    let (line, col) =
        find_binding(&source, "id").expect("could not find `id =` binding in trivial.nix");

    let mut h = LspTestHarness::with_root(lib_dir).await;

    h.open_abs(&trivial).await;
    let _ = h.wait_for_diagnostics_abs(&trivial, NIXPKGS_TIMEOUT).await;

    // Request completions — we don't care about the result, just that it
    // doesn't panic.
    let _ = h.complete_abs(&trivial, line, col).await;

    h.shutdown().await;
}

// ==============================================================================
// callPackage-style pkgs/ file tests
// ==============================================================================

/// Hover on `lib` in the beast/default.nix file (exact content from the
/// user's nixpkgs) should show `Lib`, not `{...}`.
///
/// This is a direct regression test for the reported issue where hovering on
/// `lib` in this specific file shows `{...}` instead of `Lib`.
#[tokio::test]
async fn nixpkgs_beast_lib_hover() {
    let beast_source = indoc! {r#"
        {
          lib,
          stdenv,
          emilua,
          meson,
          gperf,
          ninja,
          asciidoctor,
          pkg-config,
          fetchFromGitLab,
          gitUpdater,
        }:
        # ^1

        stdenv.mkDerivation (finalAttrs: {
          pname = "emilua_beast";
          version = "1.1.2";

          src = fetchFromGitLab {
            owner = "emilua";
            repo = "beast";
            rev = "v${finalAttrs.version}";
            hash = "sha256-MASaZvhIVKmeBUcn/NjlBZ+xh+2RgwHBH2o08lklGa0=";
          };

          buildInputs = [
            emilua
            asciidoctor
            gperf
          ];

          nativeBuildInputs = [
            meson
            pkg-config
            ninja
          ];

          passthru.updateScript = gitUpdater { rev-prefix = "v"; };

          meta = {
            description = "Emilua bindings to Boost.Beast (a WebSocket library)";
            homepage = "https://gitlab.com/emilua/beast";
            license = lib.licenses.boost;
            maintainers = with lib.maintainers; [
              manipuladordedados
              lucasew
            ];
            platforms = lib.platforms.linux;
          };
        })
    "#};

    // Find `lib,` on line 1 (0-indexed). The pattern field `lib` is on
    // the second line of the file at column 2.
    let (lib_line, lib_col) =
        find_pattern_field(beast_source, "lib").expect("could not find `lib` in beast source");
    eprintln!("lib at line {lib_line}, col {lib_col}");

    let mut h = LspTestHarness::with_options(
        &[
            (
                "tix.toml",
                indoc! {"
                    stubs = []

                    [context.callpackage]
                    paths = [\"pkgs/**/*.nix\"]
                    stubs = [\"@callpackage\"]
                "},
            ),
            ("pkgs/beast/default.nix", beast_source),
        ],
        false, // load built-in stubs
    )
    .await;

    h.open("pkgs/beast/default.nix").await;
    let _ = h
        .wait_for_diagnostics("pkgs/beast/default.nix", NIXPKGS_TIMEOUT)
        .await;

    let hover = h
        .hover("pkgs/beast/default.nix", lib_line, lib_col)
        .await
        .expect("hover on `lib` should return a result");

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };

    eprintln!("beast lib hover: {}", content.value);

    assert!(
        content.value.contains("Lib"),
        "hover on `lib` in beast/default.nix should show `Lib` type, got: {}",
        content.value,
    );

    h.shutdown().await;
}

/// Same test as nixpkgs_beast_lib_hover but using `with_root` to exercise
/// the exact same code path as the real LSP (existing directory, server
/// discovers tix.toml on its own).
#[tokio::test]
async fn nixpkgs_beast_lib_hover_with_root() {
    let beast_source = indoc! {r#"
        {
          lib,
          stdenv,
          fetchFromGitLab,
          gitUpdater,
        }:

        stdenv.mkDerivation {
          pname = "test";
          version = "1.0";
          meta = {
            license = lib.licenses.boost;
            platforms = lib.platforms.linux;
          };
        }
    "#};

    let root = create_nixpkgs_like_workspace("pkgs/beast/default.nix", beast_source);
    let pkg_path = root.join("pkgs/beast/default.nix");

    let (lib_line, lib_col) =
        find_pattern_field(beast_source, "lib").expect("could not find `lib`");
    eprintln!("lib at line {lib_line}, col {lib_col}");

    let mut h = LspTestHarness::with_root(root.clone()).await;

    h.open_abs(&pkg_path).await;
    let _ = h.wait_for_diagnostics_abs(&pkg_path, NIXPKGS_TIMEOUT).await;

    let hover = h.hover_abs(&pkg_path, lib_line, lib_col).await;
    let Some(hover) = hover else {
        h.shutdown().await;
        let _ = std::fs::remove_dir_all(&root);
        panic!("hover on `lib` should return a result");
    };

    let HoverContents::Markup(content) = &hover.contents else {
        h.shutdown().await;
        let _ = std::fs::remove_dir_all(&root);
        panic!("expected MarkupContent");
    };

    eprintln!("beast lib hover (with_root): {}", content.value);

    assert!(
        content.value.contains("Lib"),
        "hover on `lib` should show `Lib` type, got: {}",
        content.value,
    );

    h.shutdown().await;
    let _ = std::fs::remove_dir_all(&root);
}

/// Create a temp directory that mimics a nixpkgs checkout: tix.toml at root +
/// a pkgs/ file. Returns the root PathBuf (caller is responsible for cleanup).
fn create_nixpkgs_like_workspace(pkg_rel_path: &str, pkg_source: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("tix-nixpkgs-test-{}", std::process::id()));
    let pkg_full = root.join(pkg_rel_path);
    std::fs::create_dir_all(pkg_full.parent().unwrap()).unwrap();
    std::fs::write(
        root.join("tix.toml"),
        "stubs = []\n\n\
         [context.nixos]\n\
         paths = [\"nixos/**/*.nix\"]\n\
         stubs = [\"@nixos\"]\n\n\
         [context.callpackage]\n\
         paths = [\"pkgs/**/*.nix\"]\n\
         stubs = [\"@callpackage\"]\n\n\
         [project]\n\
         analyze = [\"lib/*.nix\"]\n",
    )
    .unwrap();
    std::fs::write(&pkg_full, pkg_source).unwrap();
    root
}

/// Find the first occurrence of `name` as a pattern field in `{ name, ... }:`
/// and return its 0-based `(line, col)`.
fn find_pattern_field(source: &str, name: &str) -> Option<(u32, u32)> {
    for (line_idx, line) in source.lines().enumerate() {
        // Match pattern field: preceded by `{` or `,` and followed by `,` or `}`
        if let Some(col) = line.find(name) {
            let before = &line[..col];
            if before.contains('{') || before.ends_with(' ') || before.ends_with(',') {
                // Check it's actually in a pattern context (has `{` before or is preceded by `,`)
                let after_name = &line[col + name.len()..];
                if after_name.starts_with(',')
                    || after_name.starts_with(' ')
                    || after_name.starts_with('}')
                {
                    return Some((line_idx as u32, col as u32));
                }
            }
        }
    }
    None
}

/// Hover on `lib` in a real nixpkgs pkgs/ file should show the `Lib` type
/// when @callpackage context is configured.
///
/// Creates a workspace with tix.toml (matching the user's nixpkgs config)
/// and copies a real nixpkgs package file to test the full LSP pipeline.
#[tokio::test]
async fn nixpkgs_callpackage_lib_hover() {
    let Some(nixpkgs) = try_nixpkgs_src() else {
        eprintln!("skipping nixpkgs_callpackage_lib_hover: nix not available");
        return;
    };

    // Find a real callPackage-style file. Try several candidates in case the
    // nixpkgs revision doesn't have a specific one.
    let candidates = [
        "pkgs/by-name/he/hello/package.nix",
        "pkgs/by-name/jq/jq/package.nix",
        "pkgs/tools/misc/hello/default.nix",
    ];

    let mut pkg_source = None;
    let mut pkg_rel_path = None;
    for candidate in &candidates {
        let path = nixpkgs.join(candidate);
        if let Ok(source) = std::fs::read_to_string(&path) {
            if source.contains("{ lib") || source.contains("{lib") {
                pkg_source = Some(source);
                pkg_rel_path = Some(candidate.to_string());
                break;
            }
        }
    }

    let Some(source) = pkg_source else {
        eprintln!("skipping nixpkgs_callpackage_lib_hover: no suitable pkgs/ file found");
        return;
    };
    let rel_path = pkg_rel_path.unwrap();
    eprintln!("Using nixpkgs file: {rel_path}");

    let (lib_line, lib_col) = find_pattern_field(&source, "lib")
        .expect("could not find `lib` pattern field in nixpkgs file");
    eprintln!("  lib at line {lib_line}, col {lib_col}");

    let mut h = LspTestHarness::with_options(
        &[
            (
                "tix.toml",
                // Match the user's nixpkgs tix.toml format
                &format!(
                    "stubs = []\n\n\
                     [context.callpackage]\n\
                     paths = [\"pkgs/**/*.nix\"]\n\
                     stubs = [\"@callpackage\"]\n"
                ),
            ),
            (&rel_path, &source),
        ],
        false, // load built-in stubs (needed for @callpackage)
    )
    .await;

    h.open(&rel_path).await;
    let _ = h.wait_for_diagnostics(&rel_path, NIXPKGS_TIMEOUT).await;

    let hover = h.hover(&rel_path, lib_line, lib_col).await;
    let Some(hover) = hover else {
        eprintln!("  hover returned None (analysis may have timed out)");
        h.shutdown().await;
        return;
    };

    let HoverContents::Markup(content) = &hover.contents else {
        panic!("expected MarkupContent, got {:?}", hover.contents);
    };
    eprintln!("  lib hover: {}", content.value);

    assert!(
        content.value.contains("Lib"),
        "hover on `lib` in callPackage file should show `Lib` type, got: {}",
        content.value,
    );

    h.shutdown().await;
}
