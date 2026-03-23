use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

// ==============================================================================
// Snapshot — the top-level result of a run
// ==============================================================================

#[derive(Debug, Serialize, Deserialize)]
pub struct Snapshot {
    pub version: u32,
    pub timestamp: String,
    pub tix_version: String,
    pub tix_path: String,
    pub repos: Vec<RepoResult>,
    pub summary: Summary,
}

// ==============================================================================
// Per-repo results
// ==============================================================================

#[derive(Debug, Serialize, Deserialize)]
pub struct RepoResult {
    pub name: String,
    pub url: String,
    pub rev_resolved: Option<String>,
    pub outcome: RepoOutcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub init: Option<PhaseResult>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub check: Option<PhaseResult>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub check_stats: Option<CheckStats>,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RepoOutcome {
    Clean,
    TypeErrors,
    InitFailed,
    CheckCrash,
    Timeout,
    CloneError,
    Skipped,
}

impl std::fmt::Display for RepoOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RepoOutcome::Clean => write!(f, "clean"),
            RepoOutcome::TypeErrors => write!(f, "type_errors"),
            RepoOutcome::InitFailed => write!(f, "init_failed"),
            RepoOutcome::CheckCrash => write!(f, "check_crash"),
            RepoOutcome::Timeout => write!(f, "timeout"),
            RepoOutcome::CloneError => write!(f, "clone_error"),
            RepoOutcome::Skipped => write!(f, "skipped"),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PhaseResult {
    pub exit_code: i32,
    pub duration_secs: f64,
    pub panicked: bool,
    pub timed_out: bool,
    /// Stderr output (only included if panicked or timed_out, to keep snapshots small).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Default)]
pub struct CheckStats {
    pub files_checked: usize,
    pub errors: usize,
    pub warnings: usize,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub error_codes: BTreeMap<String, usize>,
}

// ==============================================================================
// Summary
// ==============================================================================

#[derive(Debug, Serialize, Deserialize, Default)]
pub struct Summary {
    pub total: usize,
    pub clean: usize,
    pub type_errors: usize,
    pub init_failed: usize,
    pub check_crash: usize,
    pub timeout: usize,
    pub clone_error: usize,
    pub skipped: usize,
}

impl Summary {
    pub fn from_results(results: &[RepoResult]) -> Self {
        let mut s = Summary {
            total: results.len(),
            ..Default::default()
        };
        for r in results {
            match r.outcome {
                RepoOutcome::Clean => s.clean += 1,
                RepoOutcome::TypeErrors => s.type_errors += 1,
                RepoOutcome::InitFailed => s.init_failed += 1,
                RepoOutcome::CheckCrash => s.check_crash += 1,
                RepoOutcome::Timeout => s.timeout += 1,
                RepoOutcome::CloneError => s.clone_error += 1,
                RepoOutcome::Skipped => s.skipped += 1,
            }
        }
        s
    }
}

// ==============================================================================
// Helpers — parse tix check JSON output
// ==============================================================================

/// Parse the JSON output from `tix --format json check` and extract stats.
pub fn parse_check_json(json_str: &str) -> Option<CheckStats> {
    let val: serde_json::Value = serde_json::from_str(json_str).ok()?;

    let summary = val.get("summary")?;
    let files_checked = summary.get("files_checked")?.as_u64()? as usize;
    let errors = summary.get("errors")?.as_u64()? as usize;
    let warnings = summary.get("warnings")?.as_u64()? as usize;

    // Count error codes from per-file diagnostics.
    let mut error_codes: BTreeMap<String, usize> = BTreeMap::new();
    if let Some(files) = val.get("files").and_then(|f| f.as_array()) {
        for file in files {
            if let Some(diags) = file.get("diagnostics").and_then(|d| d.as_array()) {
                for diag in diags {
                    if let Some(code) = diag.get("code").and_then(|c| c.as_str()) {
                        *error_codes.entry(code.to_string()).or_default() += 1;
                    }
                }
            }
        }
    }

    Some(CheckStats {
        files_checked,
        errors,
        warnings,
        error_codes,
    })
}

/// Detect a panic in stderr output.
pub fn detect_panic(stderr: &str) -> bool {
    stderr.contains("panicked at") || stderr.contains("thread '") && stderr.contains("' panicked")
}

// ==============================================================================
// Snapshot I/O
// ==============================================================================

pub fn save_snapshot(snapshot: &Snapshot, path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let json = serde_json::to_string_pretty(snapshot)?;
    std::fs::write(path, json)?;
    Ok(())
}

pub fn load_snapshot(path: &Path) -> Result<Snapshot, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
    let snapshot: Snapshot = serde_json::from_str(&content)
        .map_err(|e| format!("failed to parse {}: {e}", path.display()))?;
    Ok(snapshot)
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_check_json_extracts_stats() {
        let json = r#"{
            "version": 1,
            "files": [
                {
                    "file": "lib/strings.nix",
                    "diagnostics": [
                        {"severity": "error", "code": "E001", "message": "type mismatch", "line": 1, "column": 1, "end_line": 1, "end_column": 5, "url": ""},
                        {"severity": "error", "code": "E001", "message": "type mismatch", "line": 2, "column": 1, "end_line": 2, "end_column": 5, "url": ""},
                        {"severity": "warning", "code": "W001", "message": "unused", "line": 3, "column": 1, "end_line": 3, "end_column": 5, "url": ""}
                    ]
                },
                {
                    "file": "lib/lists.nix",
                    "diagnostics": [
                        {"severity": "error", "code": "E003", "message": "missing attr", "line": 1, "column": 1, "end_line": 1, "end_column": 5, "url": ""}
                    ]
                }
            ],
            "summary": {
                "files_checked": 10,
                "errors": 3,
                "warnings": 1
            }
        }"#;

        let stats = parse_check_json(json).unwrap();
        assert_eq!(stats.files_checked, 10);
        assert_eq!(stats.errors, 3);
        assert_eq!(stats.warnings, 1);
        assert_eq!(stats.error_codes.get("E001"), Some(&2));
        assert_eq!(stats.error_codes.get("E003"), Some(&1));
        assert_eq!(stats.error_codes.get("W001"), Some(&1));
    }

    #[test]
    fn parse_check_json_handles_empty() {
        let json =
            r#"{"version":1,"files":[],"summary":{"files_checked":0,"errors":0,"warnings":0}}"#;
        let stats = parse_check_json(json).unwrap();
        assert_eq!(stats.files_checked, 0);
        assert!(stats.error_codes.is_empty());
    }

    #[test]
    fn parse_check_json_returns_none_for_invalid() {
        assert!(parse_check_json("not json").is_none());
        assert!(parse_check_json("{}").is_none());
    }

    #[test]
    fn detect_panic_finds_panics() {
        assert!(detect_panic("thread 'main' panicked at 'oh no'"));
        assert!(detect_panic(
            "thread 'rayon-worker' panicked at crates/lang_check/src/infer.rs"
        ));
        assert!(detect_panic("panicked at 'index out of bounds'"));
        assert!(!detect_panic("everything is fine"));
        assert!(!detect_panic(""));
    }

    #[test]
    fn summary_from_results() {
        let results = vec![
            RepoResult {
                name: "a".into(),
                url: "".into(),
                rev_resolved: None,
                outcome: RepoOutcome::Clean,
                init: None,
                check: None,
                check_stats: None,
            },
            RepoResult {
                name: "b".into(),
                url: "".into(),
                rev_resolved: None,
                outcome: RepoOutcome::TypeErrors,
                init: None,
                check: None,
                check_stats: None,
            },
            RepoResult {
                name: "c".into(),
                url: "".into(),
                rev_resolved: None,
                outcome: RepoOutcome::CheckCrash,
                init: None,
                check: None,
                check_stats: None,
            },
        ];
        let s = Summary::from_results(&results);
        assert_eq!(s.total, 3);
        assert_eq!(s.clean, 1);
        assert_eq!(s.type_errors, 1);
        assert_eq!(s.check_crash, 1);
    }

    #[test]
    fn snapshot_round_trip() {
        let snapshot = Snapshot {
            version: 1,
            timestamp: "2026-03-22T00:00:00Z".to_string(),
            tix_version: "tix 0.1.0".to_string(),
            tix_path: "/usr/bin/tix".to_string(),
            repos: vec![],
            summary: Summary::default(),
        };
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.json");
        save_snapshot(&snapshot, &path).unwrap();
        let loaded = load_snapshot(&path).unwrap();
        assert_eq!(loaded.version, 1);
        assert_eq!(loaded.tix_version, "tix 0.1.0");
    }
}
