//! Integration test for `tix stubs generate module` + context consumption.
//!
//! Exercises the full round-trip:
//!
//! 1. `tix stubs generate module --options-expr ... -o <name>.tix`
//!    (invokes nix eval → extract-options.nix → writes .tix)
//! 2. Wire up a `[context.<name>]` in tix.toml pointing at the file.
//! 3. `tix inspect modules/foo.nix --config tix.toml` picks up typed
//!    context args from the generated stub.
//!
//! Requires `nix` (a hard dev dep for tix). Not `#[ignore]`d — if nix
//! is missing the subprocess error surfaces loudly.

use indoc::indoc;
use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn tix_cli() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_tix"))
}

/// Resolve the pinned nixpkgs path via the flake. Same mechanism as
/// `nixpkgs_lib.rs::nixpkgs_src` — duplicated intentionally (see
/// SESSION.md for the shared-helper follow-up note).
fn nixpkgs_src() -> PathBuf {
    let output = Command::new("nix")
        .args(["eval", "--raw", ".#nixpkgs-src"])
        .current_dir(repo_root())
        .output()
        .expect("failed to run `nix eval` — is nix installed?");

    assert!(
        output.status.success(),
        "nix eval failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    PathBuf::from(String::from_utf8(output.stdout).unwrap().trim().to_string())
}

/// Assert that `stdout` contains a binding line matching `name :: ty_fragment`.
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

/// Generate a dummy `.tix` stub from a tiny two-option evalModules
/// expression, then consume it as a `[context.dummy]` stub and verify
/// type inference picks up the declared option types.
///
/// Fast path: the options expression loads only `lib` (no package set)
/// and has just two options, so `nix eval` completes in well under a
/// second on a warm store.
#[test]
fn generate_module_stub_from_evalmodules_and_use_it() {
    let tmp = tempfile::tempdir().expect("failed to create temp dir");
    let nixpkgs = nixpkgs_src();

    // Build the options expression by string-substituting the pinned
    // nixpkgs path. No <nixpkgs>, no env vars — the whole expression
    // is self-contained.
    let options_expr = format!(
        r#"let lib = (import {nixpkgs} {{}}).lib; in
           (lib.evalModules {{
             modules = [{{
               options.greeting = lib.mkOption {{
                 type = lib.types.str;
                 default = "hi";
                 description = "A string option";
               }};
               options.count = lib.mkOption {{
                 type = lib.types.int;
                 description = "An int option";
               }};
             }}];
           }}).options"#,
        nixpkgs = nixpkgs.display(),
    );

    // Step 1: generate the stub.
    let stub_path = tmp.path().join("dummy.tix");
    let gen_output = Command::new(tix_cli())
        .args(["stubs", "generate", "module"])
        .args(["--name", "dummy"])
        .args(["--options-expr", &options_expr])
        .args(["--context-arg", "config"])
        .arg("-o")
        .arg(&stub_path)
        .output()
        .expect("failed to run tix stubs generate module");

    let gen_stdout = String::from_utf8_lossy(&gen_output.stdout);
    let gen_stderr = String::from_utf8_lossy(&gen_output.stderr);
    assert!(
        gen_output.status.success(),
        "tix stubs generate module failed.\nstdout: {gen_stdout}\nstderr: {gen_stderr}"
    );
    assert!(
        stub_path.exists(),
        "expected dummy.tix at {}",
        stub_path.display()
    );

    // Step 2: verify the generated stub has the shape we expect. Print
    // contents on failure so missing fragments are self-evident.
    let stub_content = std::fs::read_to_string(&stub_path).unwrap();
    for fragment in [
        "type DummyConfig",
        "greeting",
        "string",
        "count",
        "int",
        "val config :: DummyConfig",
    ] {
        assert!(
            stub_content.contains(fragment),
            "generated dummy.tix missing `{fragment}`.\n--- file contents ---\n{stub_content}"
        );
    }

    // Step 3: wire up a tix.toml context pointing at the stub.
    std::fs::write(
        tmp.path().join("tix.toml"),
        indoc! {r#"
            [context.dummy]
            includes = ["modules/*.nix"]
            stubs = ["./dummy.tix"]
        "#},
    )
    .unwrap();

    // Step 4: write a module that uses config.greeting + config.count.
    std::fs::create_dir(tmp.path().join("modules")).unwrap();
    std::fs::write(
        tmp.path().join("modules/mymod.nix"),
        indoc! {"
            { config, ... }:
            {
              g = config.greeting;
              c = config.count;
            }
        "},
    )
    .unwrap();

    // Step 5: run tix inspect and verify the typed bindings came through.
    let inspect_output = Command::new(tix_cli())
        .arg("inspect")
        .arg(tmp.path().join("modules/mymod.nix"))
        .arg("--config")
        .arg(tmp.path().join("tix.toml"))
        .output()
        .expect("failed to run tix inspect");

    let inspect_stdout = String::from_utf8_lossy(&inspect_output.stdout);
    let inspect_stderr = String::from_utf8_lossy(&inspect_output.stderr);

    assert!(
        inspect_output.status.success(),
        "tix inspect failed.\nstdout: {inspect_stdout}\nstderr: {inspect_stderr}\n--- stub ---\n{stub_content}"
    );

    // `g` is `config.greeting`, which the stub types as `string`.
    assert_binding(&inspect_stdout, "g", "string");
    // `c` is `config.count`, which the stub types as `int`.
    assert_binding(&inspect_stdout, "c", "int");
}
