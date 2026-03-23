use std::path::Path;
use std::process::{Command, Stdio};

/// Shallow-clone a git repo. Returns the resolved commit SHA on success.
pub fn shallow_clone(url: &str, rev: &str, target_dir: &Path) -> Result<String, String> {
    if target_dir.exists() {
        std::fs::remove_dir_all(target_dir)
            .map_err(|e| format!("failed to remove {}: {e}", target_dir.display()))?;
    }

    // Try --branch first (works for branches and tags).
    let branch_ok = rev != "HEAD"
        && Command::new("git")
            .args(["clone", "--depth", "1", "--branch", rev, url])
            .arg(target_dir)
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .status()
            .is_ok_and(|s| s.success());

    if !branch_ok {
        // Fallback: plain clone (HEAD) then fetch the specific rev.
        if target_dir.exists() {
            let _ = std::fs::remove_dir_all(target_dir);
        }

        let status = Command::new("git")
            .args(["clone", "--depth", "1", url])
            .arg(target_dir)
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .status()
            .map_err(|e| format!("git clone failed: {e}"))?;

        if !status.success() {
            return Err(format!("git clone {url} failed"));
        }

        // If a specific rev was requested (not HEAD), fetch + checkout.
        if rev != "HEAD" {
            let status = Command::new("git")
                .args(["fetch", "--depth", "1", "origin", rev])
                .current_dir(target_dir)
                .stdout(Stdio::null())
                .stderr(Stdio::piped())
                .status()
                .map_err(|e| format!("git fetch failed: {e}"))?;

            if !status.success() {
                return Err(format!("git fetch origin {rev} failed"));
            }

            let status = Command::new("git")
                .args(["checkout", "FETCH_HEAD"])
                .current_dir(target_dir)
                .stdout(Stdio::null())
                .stderr(Stdio::piped())
                .status()
                .map_err(|e| format!("git checkout failed: {e}"))?;

            if !status.success() {
                return Err("git checkout FETCH_HEAD failed".to_string());
            }
        }
    }

    resolve_head(target_dir)
}

/// Get the HEAD commit SHA for a repo.
pub fn resolve_head(repo_dir: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo_dir)
        .output()
        .map_err(|e| format!("git rev-parse HEAD failed: {e}"))?;

    if !output.status.success() {
        return Err("git rev-parse HEAD failed".to_string());
    }

    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}
