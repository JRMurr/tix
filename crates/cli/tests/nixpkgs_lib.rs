//! Integration test: run tix-cli on every .nix file in nixpkgs `lib/`.
//!
//! Ignored by default because it requires `nix` and a nixpkgs checkout.
//! Run with: `cargo test --package cli -- --ignored nixpkgs_lib`
//!
//! The test asserts that tix-cli never *crashes* (signal, panic, segfault).
//! Type errors (exit 1) are expected and fine — we're testing robustness,
//! not correctness against nixpkgs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

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

/// Resolve the pinned nixpkgs path via `nix eval --raw .#nixpkgs-src`.
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

/// Recursively collect .nix files under `dir`, excluding `tests/` and
/// `deprecated/` path segments.
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
        } else if path.extension().map_or(false, |ext| ext == "nix") {
            out.push(path);
        }
    }
}

/// Run a command with a manual timeout (spawn + poll loop) since
/// std::process::Command doesn't have a built-in timeout.
fn run_with_timeout(cmd: &mut Command, timeout: Duration) -> Option<std::process::ExitStatus> {
    let mut child = cmd.spawn().expect("failed to spawn tix-cli");

    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Some(status),
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return None; // timeout
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => panic!("error waiting for tix-cli: {e}"),
        }
    }
}

#[derive(Default)]
struct Summary {
    pass: usize,
    type_error: usize,
    timeout: usize,
    crash: usize,
    crash_files: Vec<String>,
}

#[test]
#[ignore]
fn nixpkgs_lib() {
    let nixpkgs = nixpkgs_src();
    let lib_dir = nixpkgs.join("lib");
    assert!(lib_dir.is_dir(), "{} is not a directory", lib_dir.display());

    let nix_files = collect_nix_files(&lib_dir);
    assert!(
        !nix_files.is_empty(),
        "no .nix files found in {}",
        lib_dir.display()
    );

    eprintln!(
        "nixpkgs_lib: testing {} files in {}",
        nix_files.len(),
        lib_dir.display()
    );

    let timeout = Duration::from_secs(60);
    let mut summary = Summary::default();

    for file in &nix_files {
        let rel = file.strip_prefix(&nixpkgs).unwrap_or(file);

        let mut cmd = Command::new(tix_cli());
        cmd.arg(file)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());

        match run_with_timeout(&mut cmd, timeout) {
            Some(status) => {
                let code = status.code().unwrap_or(-1);
                match code {
                    0 => {
                        eprintln!("  PASS      {}", rel.display());
                        summary.pass += 1;
                    }
                    1 => {
                        eprintln!("  TYPE_ERR  {}", rel.display());
                        summary.type_error += 1;
                    }
                    _ => {
                        eprintln!("  CRASH({code})  {}", rel.display());
                        summary.crash += 1;
                        summary
                            .crash_files
                            .push(format!("{} (exit {code})", rel.display()));
                    }
                }
            }
            None => {
                eprintln!("  TIMEOUT   {}", rel.display());
                summary.timeout += 1;
            }
        }
    }

    // Print summary to stderr so it's visible in test output.
    eprintln!();
    eprintln!("==============================");
    eprintln!(" nixpkgs lib Summary");
    eprintln!("==============================");
    eprintln!("  Pass:       {}", summary.pass);
    eprintln!("  Type error: {}", summary.type_error);
    eprintln!("  Timeout:    {}", summary.timeout);
    eprintln!("  Crash:      {}", summary.crash);
    eprintln!("------------------------------");
    eprintln!("  Total:      {}", nix_files.len());
    eprintln!("==============================");

    if summary.crash > 0 {
        eprintln!();
        eprintln!("CRASHED FILES:");
        for cf in &summary.crash_files {
            eprintln!("  - {cf}");
        }
    }

    assert_eq!(
        summary.crash, 0,
        "{} file(s) caused tix-cli to crash",
        summary.crash
    );
}
