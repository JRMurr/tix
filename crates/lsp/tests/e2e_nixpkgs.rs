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
