use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::git;
use crate::manifest::RepoEntry;
use crate::results::{self, CheckStats, PhaseResult, RepoOutcome, RepoResult};
use crate::tix;

/// Run the full pipeline for a single repo.
pub fn run_repo(
    entry: &RepoEntry,
    cache_dir: &Path,
    tix_path: &Path,
    timeout: Duration,
    reuse_cache: bool,
) -> RepoResult {
    let repo_dir = cache_dir.join(&entry.name);

    if entry.skip {
        return skipped_result(entry);
    }

    // Phase 1: Clone
    let rev_resolved = match clone_phase(entry, &repo_dir, reuse_cache) {
        Ok(rev) => rev,
        Err(msg) => {
            eprintln!("  CLONE ERROR: {msg}");
            return RepoResult {
                name: entry.name.clone(),
                url: entry.url.clone(),
                rev_resolved: None,
                outcome: RepoOutcome::CloneError,
                init: None,
                check: None,
                check_stats: None,
                diagnostics: vec![],
            };
        }
    };

    // The working directory for tix is the repo root (or subdir if specified).
    let work_dir = match &entry.subdir {
        Some(sub) => repo_dir.join(sub),
        None => repo_dir.clone(),
    };

    if !work_dir.exists() {
        eprintln!("  ERROR: subdir {} does not exist", work_dir.display());
        return RepoResult {
            name: entry.name.clone(),
            url: entry.url.clone(),
            rev_resolved: Some(rev_resolved),
            outcome: RepoOutcome::CloneError,
            init: None,
            check: None,
            check_stats: None,
            diagnostics: vec![],
        };
    }

    // Phase 2: Init
    let (init_result, init_stdout) = if entry.skip_init {
        (None, None)
    } else {
        let (phase, stdout) = init_phase(tix_path, &work_dir, timeout);
        (Some(phase), stdout)
    };

    // Phase 3: Write tix.toml
    let tix_toml_path = work_dir.join("tix.toml");
    write_tix_toml(entry, init_stdout.as_deref(), &tix_toml_path);

    // Phase 4: Check
    let mut check = check_phase(tix_path, &work_dir, &tix_toml_path, timeout);

    // Strip absolute work_dir prefix from diagnostic file paths to keep them relative.
    let work_dir_prefix = format!("{}/", work_dir.display());
    for fd in &mut check.diagnostics {
        if let Some(rel) = fd.file.strip_prefix(&work_dir_prefix) {
            fd.file = rel.to_string();
        }
    }

    // Phase 5: Classify outcome
    let outcome = classify_outcome(&init_result, &check.phase);

    RepoResult {
        name: entry.name.clone(),
        url: entry.url.clone(),
        rev_resolved: Some(rev_resolved),
        outcome,
        init: init_result,
        check: Some(check.phase),
        check_stats: check.stats,
        diagnostics: check.diagnostics,
    }
}

// ==============================================================================
// Pipeline phases
// ==============================================================================

fn clone_phase(entry: &RepoEntry, repo_dir: &Path, reuse_cache: bool) -> Result<String, String> {
    if reuse_cache && repo_dir.exists() {
        eprintln!("  reusing cached clone");
        return git::resolve_head(repo_dir);
    }
    git::shallow_clone(&entry.url, &entry.rev, repo_dir)
}

/// Returns (PhaseResult, Option<stdout>) — stdout contains the generated tix.toml on success.
fn init_phase(
    tix_path: &Path,
    work_dir: &Path,
    timeout: Duration,
) -> (PhaseResult, Option<String>) {
    let output = match tix::run_tix(tix_path, &["init", "--dry-run", "--yes"], work_dir, timeout) {
        Ok(o) => o,
        Err(msg) => {
            eprintln!("  init spawn error: {msg}");
            return (
                PhaseResult {
                    exit_code: -1,
                    duration_secs: 0.0,
                    panicked: false,
                    timed_out: false,
                    stderr: Some(msg),
                },
                None,
            );
        }
    };

    let panicked = results::detect_panic(&output.stderr);
    let stdout = if output.exit_code == 0 && !output.stdout.trim().is_empty() {
        Some(output.stdout)
    } else {
        None
    };

    (
        PhaseResult {
            exit_code: output.exit_code,
            duration_secs: output.duration.as_secs_f64(),
            panicked,
            timed_out: output.timed_out,
            stderr: if panicked || output.timed_out {
                Some(truncate_string(&output.stderr, 4096))
            } else {
                None
            },
        },
        stdout,
    )
}

fn write_tix_toml(entry: &RepoEntry, init_stdout: Option<&str>, tix_toml_path: &PathBuf) {
    // Priority: manifest override > init output > minimal fallback.
    let content = if let Some(override_toml) = &entry.tix_toml {
        override_toml.clone()
    } else if let Some(stdout) = init_stdout {
        stdout.to_string()
    } else {
        minimal_tix_toml()
    };

    let _ = std::fs::write(tix_toml_path, content);
}

fn minimal_tix_toml() -> String {
    "[project]\nexclude = [\"**/tests/**\", \"**/test/**\"]\n".to_string()
}

struct CheckPhaseResult {
    phase: PhaseResult,
    stats: Option<CheckStats>,
    diagnostics: Vec<results::FileDiagnostics>,
}

fn check_phase(
    tix_path: &Path,
    work_dir: &Path,
    tix_toml_path: &Path,
    timeout: Duration,
) -> CheckPhaseResult {
    let config_arg = tix_toml_path.display().to_string();
    let args = vec!["--format", "json", "check", "--config", &config_arg];

    let output = match tix::run_tix(tix_path, &args, work_dir, timeout) {
        Ok(o) => o,
        Err(msg) => {
            eprintln!("  check spawn error: {msg}");
            return CheckPhaseResult {
                phase: PhaseResult {
                    exit_code: -1,
                    duration_secs: 0.0,
                    panicked: false,
                    timed_out: false,
                    stderr: Some(msg),
                },
                stats: None,
                diagnostics: vec![],
            };
        }
    };

    let panicked = results::detect_panic(&output.stderr);
    let parsed = results::parse_check_json(&output.stdout);

    let (stats, diagnostics) = match parsed {
        Some(o) => (Some(o.stats), o.diagnostics),
        None => (None, vec![]),
    };

    CheckPhaseResult {
        phase: PhaseResult {
            exit_code: output.exit_code,
            duration_secs: output.duration.as_secs_f64(),
            panicked,
            timed_out: output.timed_out,
            stderr: if panicked || output.timed_out {
                Some(truncate_string(&output.stderr, 4096))
            } else {
                None
            },
        },
        stats,
        diagnostics,
    }
}

fn classify_outcome(init_result: &Option<PhaseResult>, check_result: &PhaseResult) -> RepoOutcome {
    // If init panicked or crashed, report that.
    if let Some(init) = init_result {
        if init.panicked || init.exit_code >= 2 {
            return RepoOutcome::InitFailed;
        }
    }

    if check_result.timed_out {
        return RepoOutcome::Timeout;
    }

    if check_result.panicked || check_result.exit_code >= 2 {
        return RepoOutcome::CheckCrash;
    }

    match check_result.exit_code {
        0 => RepoOutcome::Clean,
        1 => RepoOutcome::TypeErrors,
        _ => RepoOutcome::CheckCrash,
    }
}

// ==============================================================================
// Helpers
// ==============================================================================

fn skipped_result(entry: &RepoEntry) -> RepoResult {
    RepoResult {
        name: entry.name.clone(),
        url: entry.url.clone(),
        rev_resolved: None,
        outcome: RepoOutcome::Skipped,
        init: None,
        check: None,
        check_stats: None,
        diagnostics: vec![],
    }
}

fn truncate_string(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        let mut truncated = s[..max_len].to_string();
        truncated.push_str("\n... (truncated)");
        truncated
    }
}
