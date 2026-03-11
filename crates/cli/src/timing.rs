// ==============================================================================
// Timing and memory instrumentation
// ==============================================================================
//
// Provides per-phase wall-clock timing and RSS memory snapshots for the CLI.
// Activated by `--timing`. For detailed heap profiling, build with
// `--features dhat-heap` and view the output in dhat-viewer.

use std::time::Instant;

/// Initialize the tracing subscriber (replaces env_logger).
///
/// When `show_timing` is true, enables span-level timing events so that
/// tracing spans automatically print their duration on close. Otherwise
/// falls back to the same RUST_LOG-driven behavior as before.
pub fn init_tracing(show_timing: bool) {
    use tracing_subscriber::fmt::format::FmtSpan;
    use tracing_subscriber::EnvFilter;

    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("warn,tix=info,lang_check=info,lang_ast=info"));

    let builder = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(std::io::stderr);

    if show_timing {
        builder.with_span_events(FmtSpan::CLOSE).init();
    } else {
        builder.init();
    }
}

/// Returns the current RSS (Resident Set Size) in bytes, or None if unavailable.
fn rss_bytes() -> Option<usize> {
    memory_stats::memory_stats().map(|s| s.physical_mem)
}

/// Formats bytes as a human-readable string (e.g. "42.3 MB").
fn fmt_bytes(bytes: usize) -> String {
    const KB: usize = 1024;
    const MB: usize = 1024 * KB;
    if bytes >= MB {
        format!("{:.1} MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.1} KB", bytes as f64 / KB as f64)
    } else {
        format!("{bytes} B")
    }
}

// ==============================================================================
// Phase timer — lightweight wall-clock + RSS tracker
// ==============================================================================

/// A recorded phase with its wall-clock duration and RSS snapshot.
struct Phase {
    name: &'static str,
    elapsed_ms: f64,
    rss: Option<usize>,
}

/// Tracks wall-clock time and RSS between pipeline phases.
///
/// Call `mark("name")` at each phase boundary. When `enabled` is false,
/// all operations are no-ops (zero overhead).
pub struct Timer {
    enabled: bool,
    start: Instant,
    last: Instant,
    phases: Vec<Phase>,
    start_rss: Option<usize>,
}

impl Timer {
    pub fn new(enabled: bool) -> Self {
        let now = Instant::now();
        Self {
            enabled,
            start: now,
            last: now,
            phases: Vec::new(),
            start_rss: if enabled { rss_bytes() } else { None },
        }
    }

    /// Record a phase boundary. The phase name should be a short label
    /// describing what just completed (e.g. "parse+lower", "inference").
    pub fn mark(&mut self, name: &'static str) {
        if !self.enabled {
            return;
        }
        let now = Instant::now();
        let elapsed = now.duration_since(self.last);
        self.phases.push(Phase {
            name,
            elapsed_ms: elapsed.as_secs_f64() * 1000.0,
            rss: rss_bytes(),
        });
        self.last = now;
    }

    /// Print a summary table to stderr.
    pub fn summary(&self) {
        if !self.enabled || self.phases.is_empty() {
            return;
        }

        let total_ms = self.start.elapsed().as_secs_f64() * 1000.0;

        eprintln!();
        eprintln!("Timing:");

        // Find the longest phase name for alignment.
        let max_name = self.phases.iter().map(|p| p.name.len()).max().unwrap_or(0);

        for phase in &self.phases {
            let pct = if total_ms > 0.0 {
                phase.elapsed_ms / total_ms * 100.0
            } else {
                0.0
            };
            let rss_str = phase
                .rss
                .map(|r| format!("  RSS {}", fmt_bytes(r)))
                .unwrap_or_default();
            eprintln!(
                "  {:<width$}  {:>8.1} ms  ({:>4.1}%){rss_str}",
                phase.name,
                phase.elapsed_ms,
                pct,
                width = max_name,
            );
        }

        let rss_delta = match (self.start_rss, self.phases.last().and_then(|p| p.rss)) {
            (Some(start), Some(end)) if end > start => {
                format!("  (RSS delta: +{})", fmt_bytes(end - start))
            }
            _ => String::new(),
        };

        eprintln!(
            "  {:<width$}  {:>8.1} ms{rss_delta}",
            "total",
            total_ms,
            width = max_name,
        );
    }
}
