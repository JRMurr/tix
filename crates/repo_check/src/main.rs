mod diff;
mod git;
mod manifest;
mod results;
mod runner;
mod tix;

use std::path::PathBuf;
use std::time::Duration;

use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[command(
    name = "tix-repo-check",
    about = "Test tix against real-world Nix repos"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Run tix against all repos in the manifest
    Run {
        /// Path to manifest file
        #[arg(long, default_value = "repo-check.toml")]
        manifest: PathBuf,

        /// Path to the tix binary (default: auto-build from repo)
        #[arg(long)]
        tix_path: Option<PathBuf>,

        /// Output snapshot path (default: repo-check-results/<timestamp>.json)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Only run these repos (comma-separated names)
        #[arg(long, value_delimiter = ',')]
        only: Option<Vec<String>>,

        /// Build tix in release mode
        #[arg(long)]
        release: bool,

        /// Per-repo timeout in seconds (overrides manifest)
        #[arg(long)]
        timeout: Option<u64>,

        /// Reuse cached clones instead of re-cloning
        #[arg(long)]
        reuse_cache: bool,
    },

    /// Compare two snapshot files and report regressions
    Diff {
        /// Baseline snapshot (older)
        baseline: PathBuf,
        /// Current snapshot (newer)
        current: PathBuf,
    },

    /// List repos in a manifest
    List {
        /// Path to manifest file
        #[arg(long, default_value = "repo-check.toml")]
        manifest: PathBuf,
    },

    /// Clean the cache directory
    Clean {
        /// Path to manifest file
        #[arg(long, default_value = "repo-check.toml")]
        manifest: PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Run {
            manifest,
            tix_path,
            output,
            only,
            release,
            timeout,
            reuse_cache,
        } => cmd_run(
            &manifest,
            tix_path.as_deref(),
            output.as_deref(),
            only.as_deref(),
            release,
            timeout,
            reuse_cache,
        ),
        Command::Diff { baseline, current } => cmd_diff(&baseline, &current),
        Command::List { manifest } => cmd_list(&manifest),
        Command::Clean { manifest } => cmd_clean(&manifest),
    };

    if let Err(e) = result {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

// ==============================================================================
// Subcommands
// ==============================================================================

fn cmd_run(
    manifest_path: &std::path::Path,
    tix_path_arg: Option<&std::path::Path>,
    output_path: Option<&std::path::Path>,
    only: Option<&[String]>,
    release: bool,
    timeout_override: Option<u64>,
    reuse_cache: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let manifest = manifest::load_manifest(manifest_path)?;

    // Resolve tix binary.
    let tix_path = tix::resolve_tix(tix_path_arg, release)?;
    let tix_version = tix::tix_version(&tix_path);
    eprintln!("tix: {tix_version} ({})", tix_path.display());

    // Ensure cache dir exists and resolve to absolute path.
    let cache_dir = &manifest.settings.cache_dir;
    std::fs::create_dir_all(cache_dir)?;
    let cache_dir = std::fs::canonicalize(cache_dir)?;

    let timeout_secs = timeout_override.unwrap_or(manifest.settings.timeout_secs);
    let timeout = Duration::from_secs(timeout_secs);

    // Filter repos if --only is specified.
    let repos: Vec<&manifest::RepoEntry> = manifest
        .repos
        .iter()
        .filter(|r| only.is_none_or(|names| names.iter().any(|n| n == &r.name)))
        .collect();

    eprintln!("Running {} repos (timeout: {timeout_secs}s)\n", repos.len());

    // Run each repo sequentially.
    let mut repo_results = Vec::new();
    for (i, entry) in repos.iter().enumerate() {
        eprintln!("[{}/{}] {}", i + 1, repos.len(), entry.name,);

        let result = runner::run_repo(entry, &cache_dir, &tix_path, timeout, reuse_cache);
        print_repo_summary(&result);
        repo_results.push(result);
    }

    // Build snapshot.
    let summary = results::Summary::from_results(&repo_results);
    let timestamp = now_iso8601();
    let snapshot = results::Snapshot {
        version: 1,
        timestamp: timestamp.clone(),
        tix_version: tix_version.clone(),
        tix_path: tix_path.display().to_string(),
        repos: repo_results,
        summary,
    };

    // Determine output path.
    let out_path = match output_path {
        Some(p) => p.to_path_buf(),
        None => {
            let dir = PathBuf::from("repo-check-results");
            // Use a filesystem-safe timestamp.
            let safe_ts = timestamp.replace(':', "-").replace('T', "_");
            dir.join(format!("{safe_ts}.json"))
        }
    };

    results::save_snapshot(&snapshot, &out_path)?;
    eprintln!("\nSnapshot saved: {}", out_path.display());

    // Print summary.
    eprintln!();
    print_summary(&snapshot.summary);

    // Exit 1 if any crashes occurred (useful for CI).
    if snapshot.summary.check_crash > 0 || snapshot.summary.init_failed > 0 {
        std::process::exit(1);
    }

    Ok(())
}

fn cmd_diff(
    baseline_path: &std::path::Path,
    current_path: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let baseline = results::load_snapshot(baseline_path)?;
    let current = results::load_snapshot(current_path)?;
    let report = diff::diff_snapshots(&baseline, &current);
    print!("{}", diff::format_diff(&report));

    // Exit 1 if there are regressions.
    if !report.regressions.is_empty() {
        std::process::exit(1);
    }
    Ok(())
}

fn cmd_list(manifest_path: &std::path::Path) -> Result<(), Box<dyn std::error::Error>> {
    let manifest = manifest::load_manifest(manifest_path)?;
    println!("{:<24} URL", "NAME");
    println!("{}", "-".repeat(72));
    for repo in &manifest.repos {
        let skip_marker = if repo.skip { " (skip)" } else { "" };
        println!("{:<24} {}{}", repo.name, repo.url, skip_marker);
    }
    println!("\n{} repos total", manifest.repos.len());
    Ok(())
}

fn cmd_clean(manifest_path: &std::path::Path) -> Result<(), Box<dyn std::error::Error>> {
    let manifest = manifest::load_manifest(manifest_path)?;
    let cache_dir = &manifest.settings.cache_dir;
    if cache_dir.exists() {
        eprintln!("Removing {}", cache_dir.display());
        std::fs::remove_dir_all(cache_dir)?;
    } else {
        eprintln!("Cache directory does not exist: {}", cache_dir.display());
    }
    Ok(())
}

// ==============================================================================
// Display helpers
// ==============================================================================

fn print_repo_summary(result: &results::RepoResult) {
    let status = match result.outcome {
        results::RepoOutcome::Clean => "\x1b[32mCLEAN\x1b[0m",
        results::RepoOutcome::TypeErrors => "\x1b[33mTYPE_ERRORS\x1b[0m",
        results::RepoOutcome::InitFailed => "\x1b[31mINIT_FAILED\x1b[0m",
        results::RepoOutcome::CheckCrash => "\x1b[31;1mCHECK_CRASH\x1b[0m",
        results::RepoOutcome::Timeout => "\x1b[31mTIMEOUT\x1b[0m",
        results::RepoOutcome::CloneError => "\x1b[31mCLONE_ERROR\x1b[0m",
        results::RepoOutcome::Skipped => "\x1b[90mSKIPPED\x1b[0m",
    };

    let stats = result
        .check_stats
        .as_ref()
        .map(|s| {
            format!(
                " ({} files, {} errors, {} warnings)",
                s.files_checked, s.errors, s.warnings
            )
        })
        .unwrap_or_default();

    let duration = result
        .check
        .as_ref()
        .map(|c| format!(", {:.1}s", c.duration_secs))
        .unwrap_or_default();

    eprintln!("  {status}{stats}{duration}");
}

fn print_summary(summary: &results::Summary) {
    eprintln!("=== Summary ===");
    eprintln!("  Total:       {}", summary.total);
    eprintln!("  Clean:       {}", summary.clean);
    eprintln!("  Type errors: {}", summary.type_errors);
    if summary.init_failed > 0 {
        eprintln!("  Init failed: {}", summary.init_failed);
    }
    if summary.check_crash > 0 {
        eprintln!("  Crashes:     {}", summary.check_crash);
    }
    if summary.timeout > 0 {
        eprintln!("  Timeouts:    {}", summary.timeout);
    }
    if summary.clone_error > 0 {
        eprintln!("  Clone errors:{}", summary.clone_error);
    }
    if summary.skipped > 0 {
        eprintln!("  Skipped:     {}", summary.skipped);
    }
}

fn now_iso8601() -> String {
    // Use std::time to avoid chrono dependency.
    let now = std::time::SystemTime::now();
    let secs = now
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();

    // Convert to UTC date-time manually.
    // This is approximate but sufficient for snapshot filenames.
    let days = secs / 86400;
    let time_of_day = secs % 86400;
    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;

    // Simple days-since-epoch to date. Accurate for 2000-2099.
    let mut y = 1970;
    let mut remaining_days = days;
    loop {
        let days_in_year = if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) {
            366
        } else {
            365
        };
        if remaining_days < days_in_year {
            break;
        }
        remaining_days -= days_in_year;
        y += 1;
    }

    let leap = y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
    let month_days: [u64; 12] = if leap {
        [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    } else {
        [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    };

    let mut m = 0;
    for (i, &md) in month_days.iter().enumerate() {
        if remaining_days < md {
            m = i;
            break;
        }
        remaining_days -= md;
    }

    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        y,
        m + 1,
        remaining_days + 1,
        hours,
        minutes,
        seconds
    )
}
