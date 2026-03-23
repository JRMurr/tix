use std::collections::HashMap;

use crate::results::{RepoOutcome, Snapshot};

pub struct DiffReport {
    pub baseline_timestamp: String,
    pub current_timestamp: String,
    pub baseline_tix_version: String,
    pub current_tix_version: String,
    pub regressions: Vec<Change>,
    pub improvements: Vec<Change>,
    pub unchanged: usize,
    pub new_repos: usize,
    pub removed_repos: usize,
}

pub struct Change {
    pub repo: String,
    pub was: RepoOutcome,
    pub now: RepoOutcome,
    pub error_delta: Option<i64>,
}

/// Compare two snapshots and produce a diff report.
pub fn diff_snapshots(baseline: &Snapshot, current: &Snapshot) -> DiffReport {
    let baseline_map: HashMap<&str, _> = baseline
        .repos
        .iter()
        .map(|r| (r.name.as_str(), r))
        .collect();
    let current_map: HashMap<&str, _> =
        current.repos.iter().map(|r| (r.name.as_str(), r)).collect();

    let mut regressions = Vec::new();
    let mut improvements = Vec::new();
    let mut unchanged = 0;
    let mut new_repos = 0;
    let mut removed_repos = 0;

    // Check repos in current against baseline.
    for repo in &current.repos {
        let Some(base) = baseline_map.get(repo.name.as_str()) else {
            new_repos += 1;
            continue;
        };

        if repo.outcome == base.outcome {
            unchanged += 1;
            continue;
        }

        let error_delta = match (&base.check_stats, &repo.check_stats) {
            (Some(b), Some(c)) => Some(c.errors as i64 - b.errors as i64),
            _ => None,
        };

        let severity_now = outcome_severity(repo.outcome);
        let severity_was = outcome_severity(base.outcome);

        if severity_now > severity_was {
            regressions.push(Change {
                repo: repo.name.clone(),
                was: base.outcome,
                now: repo.outcome,
                error_delta,
            });
        } else {
            improvements.push(Change {
                repo: repo.name.clone(),
                was: base.outcome,
                now: repo.outcome,
                error_delta,
            });
        }
    }

    // Count repos removed from current.
    for name in baseline_map.keys() {
        if !current_map.contains_key(name) {
            removed_repos += 1;
        }
    }

    DiffReport {
        baseline_timestamp: baseline.timestamp.clone(),
        current_timestamp: current.timestamp.clone(),
        baseline_tix_version: baseline.tix_version.clone(),
        current_tix_version: current.tix_version.clone(),
        regressions,
        improvements,
        unchanged,
        new_repos,
        removed_repos,
    }
}

/// Lower is better. Used to classify changes as regressions vs improvements.
fn outcome_severity(outcome: RepoOutcome) -> u8 {
    match outcome {
        RepoOutcome::Clean => 0,
        RepoOutcome::TypeErrors => 1,
        RepoOutcome::Skipped => 2,
        RepoOutcome::CloneError => 3,
        RepoOutcome::InitFailed => 4,
        RepoOutcome::Timeout => 5,
        RepoOutcome::CheckCrash => 6,
    }
}

/// Format the diff report as human-readable text.
pub fn format_diff(report: &DiffReport) -> String {
    let mut out = String::new();

    out.push_str(&format!(
        "Comparing: {} vs {}\n",
        report.baseline_timestamp, report.current_timestamp
    ));
    out.push_str(&format!(
        "tix: {} vs {}\n\n",
        report.baseline_tix_version, report.current_tix_version
    ));

    if report.regressions.is_empty() {
        out.push_str("REGRESSIONS: none\n\n");
    } else {
        out.push_str(&format!("REGRESSIONS ({}):\n", report.regressions.len()));
        for r in &report.regressions {
            let delta = r
                .error_delta
                .map(|d| format!(" ({:+} errors)", d))
                .unwrap_or_default();
            out.push_str(&format!("  {}: {} -> {}{}\n", r.repo, r.was, r.now, delta));
        }
        out.push('\n');
    }

    if report.improvements.is_empty() {
        out.push_str("IMPROVEMENTS: none\n\n");
    } else {
        out.push_str(&format!("IMPROVEMENTS ({}):\n", report.improvements.len()));
        for i in &report.improvements {
            let delta = i
                .error_delta
                .map(|d| format!(" ({:+} errors)", d))
                .unwrap_or_default();
            out.push_str(&format!("  {}: {} -> {}{}\n", i.repo, i.was, i.now, delta));
        }
        out.push('\n');
    }

    out.push_str(&format!("UNCHANGED: {}\n", report.unchanged));

    if report.new_repos > 0 {
        out.push_str(&format!("NEW REPOS: {}\n", report.new_repos));
    }
    if report.removed_repos > 0 {
        out.push_str(&format!("REMOVED REPOS: {}\n", report.removed_repos));
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::results::{RepoResult, Summary};

    fn make_snapshot(repos: Vec<RepoResult>, timestamp: &str, version: &str) -> Snapshot {
        let summary = Summary::from_results(&repos);
        Snapshot {
            version: 1,
            timestamp: timestamp.to_string(),
            tix_version: version.to_string(),
            tix_path: "/bin/tix".to_string(),
            repos,
            summary,
        }
    }

    fn repo(name: &str, outcome: RepoOutcome) -> RepoResult {
        RepoResult {
            name: name.to_string(),
            url: String::new(),
            rev_resolved: None,
            outcome,
            init: None,
            check: None,
            check_stats: None,
        }
    }

    #[test]
    fn no_changes() {
        let baseline = make_snapshot(
            vec![
                repo("a", RepoOutcome::Clean),
                repo("b", RepoOutcome::TypeErrors),
            ],
            "t1",
            "v1",
        );
        let current = make_snapshot(
            vec![
                repo("a", RepoOutcome::Clean),
                repo("b", RepoOutcome::TypeErrors),
            ],
            "t2",
            "v2",
        );
        let report = diff_snapshots(&baseline, &current);
        assert!(report.regressions.is_empty());
        assert!(report.improvements.is_empty());
        assert_eq!(report.unchanged, 2);
    }

    #[test]
    fn regression_detected() {
        let baseline = make_snapshot(vec![repo("a", RepoOutcome::TypeErrors)], "t1", "v1");
        let current = make_snapshot(vec![repo("a", RepoOutcome::CheckCrash)], "t2", "v2");
        let report = diff_snapshots(&baseline, &current);
        assert_eq!(report.regressions.len(), 1);
        assert_eq!(report.regressions[0].repo, "a");
        assert!(report.improvements.is_empty());
    }

    #[test]
    fn improvement_detected() {
        let baseline = make_snapshot(vec![repo("a", RepoOutcome::CheckCrash)], "t1", "v1");
        let current = make_snapshot(vec![repo("a", RepoOutcome::TypeErrors)], "t2", "v2");
        let report = diff_snapshots(&baseline, &current);
        assert!(report.regressions.is_empty());
        assert_eq!(report.improvements.len(), 1);
        assert_eq!(report.improvements[0].repo, "a");
    }

    #[test]
    fn new_and_removed_repos() {
        let baseline = make_snapshot(vec![repo("old", RepoOutcome::Clean)], "t1", "v1");
        let current = make_snapshot(vec![repo("new", RepoOutcome::Clean)], "t2", "v2");
        let report = diff_snapshots(&baseline, &current);
        assert_eq!(report.new_repos, 1);
        assert_eq!(report.removed_repos, 1);
        assert_eq!(report.unchanged, 0);
    }
}
