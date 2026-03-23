use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Resolve the tix binary path.
///
/// Resolution order:
/// 1. Explicit `--tix-path` flag
/// 2. `TIX_PATH` env var
/// 3. Auto `cargo build --bin tix` from repo root
pub fn resolve_tix(
    explicit_path: Option<&Path>,
    release: bool,
) -> Result<PathBuf, Box<dyn std::error::Error>> {
    if let Some(p) = explicit_path {
        if !p.exists() {
            return Err(format!("tix binary not found at {}", p.display()).into());
        }
        return Ok(p.to_path_buf());
    }

    if let Ok(p) = std::env::var("TIX_PATH") {
        let path = PathBuf::from(&p);
        if path.exists() {
            return Ok(path);
        }
        eprintln!("warning: TIX_PATH={p} does not exist, falling back to cargo build");
    }

    // Auto-build from repo root.
    if !Path::new("Cargo.toml").exists() {
        return Err("not in tix repo root and no --tix-path specified".into());
    }

    let profile = if release { "release" } else { "debug" };
    eprintln!("Building tix ({profile})...");

    let mut cmd = Command::new("cargo");
    cmd.args(["build", "--bin", "tix"]);
    if release {
        cmd.arg("--release");
    }
    let status = cmd.status()?;
    if !status.success() {
        return Err("cargo build --bin tix failed".into());
    }

    let path = PathBuf::from(format!("target/{profile}/tix"));
    std::fs::canonicalize(&path)
        .map_err(|e| format!("tix binary not found at {}: {e}", path.display()).into())
}

/// Get the tix version string.
pub fn tix_version(tix_path: &Path) -> String {
    Command::new(tix_path)
        .arg("--version")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .unwrap_or_else(|| "unknown".to_string())
        .trim()
        .to_string()
}

/// Output captured from a tix subprocess.
pub struct TixOutput {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub duration: Duration,
    pub timed_out: bool,
}

/// Cap for captured output to avoid OOM.
const MAX_OUTPUT_BYTES: usize = 10 * 1024 * 1024; // 10 MB

/// Run a tix command with a timeout. Returns captured output.
pub fn run_tix(
    tix_path: &Path,
    args: &[&str],
    working_dir: &Path,
    timeout: Duration,
) -> Result<TixOutput, String> {
    let start = Instant::now();

    let mut child = Command::new(tix_path)
        .args(args)
        .current_dir(working_dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn tix: {e}"))?;

    // Poll until complete or timeout. Print elapsed time every 30s so it
    // doesn't look stuck on slow repos.
    let mut last_tick = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let duration = start.elapsed();
                let mut stdout = String::new();
                let mut stderr = String::new();
                if let Some(out) = child.stdout.take() {
                    let _ = out
                        .take(MAX_OUTPUT_BYTES as u64)
                        .read_to_string(&mut stdout);
                }
                if let Some(err) = child.stderr.take() {
                    let _ = err
                        .take(MAX_OUTPUT_BYTES as u64)
                        .read_to_string(&mut stderr);
                }

                return Ok(TixOutput {
                    exit_code: status.code().unwrap_or(-1),
                    stdout,
                    stderr,
                    duration,
                    timed_out: false,
                });
            }
            Ok(None) => {
                let elapsed = start.elapsed();
                if elapsed > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Ok(TixOutput {
                        exit_code: -1,
                        stdout: String::new(),
                        stderr: "timed out".to_string(),
                        duration: start.elapsed(),
                        timed_out: true,
                    });
                }
                // Print a tick every 30s so long-running checks don't look stuck.
                if last_tick.elapsed() >= Duration::from_secs(30) {
                    eprint!("  ... {:.0}s\r", elapsed.as_secs_f64());
                    last_tick = Instant::now();
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => return Err(format!("error waiting for tix: {e}")),
        }
    }
}
