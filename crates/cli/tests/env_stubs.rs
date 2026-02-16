//! Integration tests for the `TIX_BUILTIN_STUBS` environment variable override.
//!
//! These run `tix-cli` as a subprocess so each test gets an isolated environment —
//! no risk of env var pollution between parallel test threads.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Repo root, derived from Cargo's `CARGO_MANIFEST_DIR` (crates/cli).
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn tix_cli() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_tix-cli"))
}

/// Write minimal NixOS context stubs to a temp directory and verify that
/// `tix-cli` picks them up via `TIX_BUILTIN_STUBS` when processing a file
/// matched by `stubs = ["@nixos"]` in tix.toml.
#[test]
fn builtin_stubs_env_override_nixos() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // Minimal nixos.tix — just enough types for test/nixos_module.nix which
    // accesses config, lib (mkEnableOption, mkOption, id), and pkgs.
    std::fs::write(
        tmp.path().join("nixos.tix"),
        r#"
type NixosConfig = { ... };
type Lib = {
    mkEnableOption: string -> bool,
    mkOption: { ... } -> a,
    id: a -> a,
    ...
};
type Pkgs = { ... };

val config :: NixosConfig;
val lib :: Lib;
val pkgs :: Pkgs;
"#,
    )
    .unwrap();

    let output = Command::new(tix_cli())
        .arg(root.join("test/nixos_module.nix"))
        .arg("--config")
        .arg(root.join("test/tix.toml"))
        .env("TIX_BUILTIN_STUBS", tmp.path())
        .output()
        .expect("failed to run tix-cli");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "tix-cli failed with override nixos stubs.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("config"),
        "expected 'config' binding in output.\nstdout: {stdout}"
    );
}

/// Same idea for the `@home-manager` context, using the nixos_fixture layout.
#[test]
fn builtin_stubs_env_override_home_manager() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // Minimal home-manager.tix — shell.nix accesses config.programs.fish.enable.
    std::fs::write(
        tmp.path().join("home-manager.tix"),
        r#"
type HomeManagerConfig = {
    programs: {
        fish: { enable: bool, ... },
        ...
    },
    ...
};
type Lib = { ... };
type Pkgs = { ... };

val config :: HomeManagerConfig;
val lib :: Lib;
val pkgs :: Pkgs;
val osConfig :: { ... };
"#,
    )
    .unwrap();

    let output = Command::new(tix_cli())
        .arg(root.join("test/nixos_fixture/home/shell.nix"))
        .arg("--config")
        .arg(root.join("test/nixos_fixture/tix.toml"))
        .env("TIX_BUILTIN_STUBS", tmp.path())
        .output()
        .expect("failed to run tix-cli");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "tix-cli failed with override home-manager stubs.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("config"),
        "expected 'config' binding in output.\nstdout: {stdout}"
    );
}

/// When `TIX_BUILTIN_STUBS` is unset, the compiled-in stubs should be used
/// as a fallback. Verify the binary still type-checks successfully.
#[test]
fn builtin_stubs_fallback_without_env() {
    let root = repo_root();

    let output = Command::new(tix_cli())
        .arg(root.join("test/nixos_module.nix"))
        .arg("--config")
        .arg(root.join("test/tix.toml"))
        .env_remove("TIX_BUILTIN_STUBS")
        .output()
        .expect("failed to run tix-cli");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "tix-cli failed without TIX_BUILTIN_STUBS (compiled-in fallback).\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("config"),
        "expected 'config' binding in output.\nstdout: {stdout}"
    );
}
