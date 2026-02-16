//! Integration tests for the `TIX_BUILTIN_STUBS` environment variable override.
//!
//! These run `tix-cli` as a subprocess so each test gets an isolated environment —
//! no risk of env var pollution between parallel test threads.

use indoc::indoc;
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

/// Assert that `stdout` contains a binding line matching `name :: ty_fragment`.
/// The type fragment is checked as a substring of the type portion, so you can
/// match `config :: NixosConfig` without spelling out the full expanded type.
fn assert_binding(stdout: &str, name: &str, ty_fragment: &str) {
    let binding_prefix = format!("{name} :: ");
    let matching_line = stdout.lines().find(|l| {
        let trimmed = l.trim();
        trimmed.starts_with(&binding_prefix)
    });
    match matching_line {
        Some(line) => {
            let ty_part = line.trim().strip_prefix(&binding_prefix).unwrap();
            assert!(
                ty_part.contains(ty_fragment),
                "binding `{name}` has type `{ty_part}`, expected it to contain `{ty_fragment}`\nfull stdout:\n{stdout}"
            );
        }
        None => {
            panic!("expected binding `{name}` in output, but not found.\nstdout:\n{stdout}");
        }
    }
}

/// Write minimal NixOS context stubs to a temp directory and verify that
/// `tix-cli` picks them up via `TIX_BUILTIN_STUBS` when processing a file
/// matched by `stubs = ["@nixos"]` in tix.toml.
///
/// Checks that the stubs actually affect type inference — `config` gets the
/// alias type, `lib.id "hello"` resolves to `string`, etc.
#[test]
fn builtin_stubs_env_override_nixos() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // Minimal nixos.tix — just enough types for test/nixos_module.nix which
    // accesses config, lib (mkEnableOption, mkOption, id), and pkgs.
    std::fs::write(
        tmp.path().join("nixos.tix"),
        indoc! {"
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
        "},
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

    // Verify that stubs actually fed types into inference.
    assert_binding(&stdout, "config", "NixosConfig");
    assert_binding(&stdout, "lib", "Lib");
    assert_binding(&stdout, "pkgs", "Pkgs");
    // `lib.id "hello"` should resolve to string via the `id: a -> a` stub.
    assert_binding(&stdout, "greeting", "string");
    // `lib.mkEnableOption "my-service"` should resolve to bool.
    assert_binding(&stdout, "enable", "bool");
}

/// Same idea for the `@home-manager` context, using the nixos_fixture layout.
///
/// Verifies that config field access (`config.programs.fish.enable`) resolves
/// through the stub-declared `HomeManagerConfig` type.
#[test]
fn builtin_stubs_env_override_home_manager() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // Minimal home-manager.tix — shell.nix accesses config.programs.fish.enable.
    std::fs::write(
        tmp.path().join("home-manager.tix"),
        indoc! {"
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
        "},
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

    // Verify stub types propagated through field access.
    assert_binding(&stdout, "config", "HomeManagerConfig");
    assert_binding(&stdout, "lib", "Lib");
    assert_binding(&stdout, "pkgs", "Pkgs");
    // `config.programs.fish.enable` should resolve to `bool`.
    assert_binding(&stdout, "enable", "bool");
    // `config.programs.fish` should contain the `enable: bool` field.
    assert_binding(&stdout, "fish", "enable: bool");
}

/// When `TIX_BUILTIN_STUBS` is unset, the compiled-in stubs should be used
/// as a fallback. Verify the binary still type-checks successfully and produces
/// the same types as the override path.
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

    // Same type assertions as the override test — compiled-in stubs should
    // produce equivalent results.
    assert_binding(&stdout, "config", "NixosConfig");
    assert_binding(&stdout, "lib", "Lib");
    assert_binding(&stdout, "greeting", "string");
}

/// Verify that modules declared in `--stubs` files merge with modules from
/// the compiled-in builtins (`stubs/lib.tix`). The builtin `module lib`
/// defines e.g. `val id :: a -> a`; a local stub adds `val customFn :: int -> string`.
/// Both should be accessible through `lib.id` and `lib.customFn` respectively.
#[test]
fn module_merge_builtins_and_local_stubs() {
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // A local stub that extends module lib with a custom function.
    // This should merge with the built-in lib module from stubs/lib.tix.
    let custom_stub = tmp.path().join("custom.tix");
    std::fs::write(
        &custom_stub,
        indoc! {"
            module lib {
                val customFn :: int -> string;
            }
        "},
    )
    .unwrap();

    // Minimal nixos.tix context stubs — reference the merged Lib type.
    let stubs_dir = tmp.path().join("builtin_stubs");
    std::fs::create_dir(&stubs_dir).unwrap();
    std::fs::write(
        stubs_dir.join("nixos.tix"),
        indoc! {"
            type NixosConfig = { ... };
            type Pkgs = { ... };

            val config :: NixosConfig;
            val lib :: Lib;
            val pkgs :: Pkgs;
        "},
    )
    .unwrap();

    // tix.toml — context definition matching our test Nix file.
    let config_path = tmp.path().join("tix.toml");
    std::fs::write(
        &config_path,
        indoc! {r#"
            [context.nixos]
            paths = ["merge_test.nix"]
            stubs = ["@nixos"]
        "#},
    )
    .unwrap();

    // Nix file that uses both the builtin lib.id and the locally-added
    // lib.customFn, exercising the merged Lib type end-to-end.
    let nix_file = tmp.path().join("merge_test.nix");
    std::fs::write(
        &nix_file,
        indoc! {"
            { config, lib, pkgs, ... }:
            {
              greeting = lib.id \"hello\";
              converted = lib.customFn 42;
            }
        "},
    )
    .unwrap();

    let output = Command::new(tix_cli())
        .arg(&nix_file)
        .arg("--stubs")
        .arg(&custom_stub)
        .arg("--config")
        .arg(&config_path)
        .env("TIX_BUILTIN_STUBS", &stubs_dir)
        .output()
        .expect("failed to run tix-cli");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "tix-cli failed with merged stubs.\nstdout: {stdout}\nstderr: {stderr}"
    );

    // lib.id "hello" should resolve to string (from builtin stubs/lib.tix).
    assert_binding(&stdout, "greeting", "string");
    // lib.customFn 42 should resolve to string (from local --stubs file).
    assert_binding(&stdout, "converted", "string");
}

/// Verify that deliberately wrong stubs cause a type error, proving the stubs
/// actually influence inference rather than being silently ignored.
#[test]
fn wrong_stubs_cause_type_error() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("failed to create temp dir");

    // Declare lib as `int` — `lib.id "hello"` should fail because you can't
    // access fields on an int.
    std::fs::write(
        tmp.path().join("nixos.tix"),
        indoc! {"
            val config :: int;
            val lib :: int;
            val pkgs :: int;
        "},
    )
    .unwrap();

    let output = Command::new(tix_cli())
        .arg(root.join("test/nixos_module.nix"))
        .arg("--config")
        .arg(root.join("test/tix.toml"))
        .env("TIX_BUILTIN_STUBS", tmp.path())
        .output()
        .expect("failed to run tix-cli");

    assert!(
        !output.status.success(),
        "tix-cli should have failed with wrong stubs but succeeded.\nstdout: {}",
        String::from_utf8_lossy(&output.stdout)
    );
}
