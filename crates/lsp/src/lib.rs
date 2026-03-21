mod code_actions;
mod completion;
mod config;
pub mod convert;
mod diagnostics;
mod document_highlight;
mod document_link;
mod document_symbol;
mod formatting;
mod goto_def;
mod hover;
mod inlay_hint;
#[cfg(test)]
mod pbt;
pub mod project_config;
mod references;
mod rename;
mod selection_range;
mod semantic_tokens;
pub mod server;
mod signature_help;
mod state;
pub mod store_stubs;
pub mod test_util;
mod ty_nav;
mod type_def;
mod warmup;
mod workspace_symbols;

use lang_check::aliases::TypeAliasRegistry;
#[cfg(unix)]
use rlimit::Resource;
use tower_lsp::{LspService, Server};

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
pub fn load_stubs(
    registry: &mut TypeAliasRegistry,
    path: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                if let Some(name) = entry_path.file_name().and_then(|n| n.to_str()) {
                    if comment_parser::SKIP_STUB_DIRS.contains(&name) {
                        continue;
                    }
                }
                load_stubs(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                let source = std::fs::read_to_string(&entry_path)?;
                let file = comment_parser::parse_tix_file(&source)
                    .map_err(|e| format!("Error parsing {}: {e}", entry_path.display()))?;
                registry.load_tix_file_with_path(&file, &entry_path);
            }
        }
    } else {
        let source = std::fs::read_to_string(path)?;
        let file = comment_parser::parse_tix_file(&source)
            .map_err(|e| format!("Error parsing {}: {e}", path.display()))?;
        registry.load_tix_file_with_path(&file, path);
    }
    Ok(())
}

/// Run the Tix LSP server. Builds a tokio runtime with large stack sizes
/// (16 MB per worker) to handle deep import trees, initializes logging,
/// and serves on stdin/stdout.
///
/// Stubs are loaded from `tix.toml` (discovered from the workspace root)
/// and editor settings (`nix.serverSettings.stubs`). Built-in nixpkgs stubs
/// are always included; use `TIX_BUILTIN_STUBS` env var to override the
/// compiled-in context stubs with richer generated ones.
/// `mem_limit_override`: if `Some(mib)`, use that value as the memory limit
/// instead of reading `TIX_MEM_LIMIT` from the environment. `Some(0)` disables
/// the limit entirely.
/// `log_level_override`: if `Some(level)`, use that level for tix crates
/// instead of the default "info". Common values: "debug", "trace", "warn".
/// The RUST_LOG env var takes precedence if set.
pub fn run_lsp(mem_limit_override: Option<u64>, log_level_override: Option<String>) {
    // Build a custom tokio runtime with 16MB worker thread stacks. The default
    // (~8MB on Linux) can overflow on deep import trees where file_root_type
    // recurses through many transitive imports, each allocating Module,
    // NameResolution, CheckCtx, etc. on the stack.
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(16 * 1024 * 1024)
        .build()
        .expect("failed to build tokio runtime");
    rt.block_on(async_lsp_main(mem_limit_override, log_level_override));
}

async fn async_lsp_main(mem_limit_override: Option<u64>, log_level_override: Option<String>) {
    // Default to info-level for tix/lang crates, warn for everything else.
    // RUST_LOG env var overrides this if set. The --log-level CLI flag
    // changes the tix crate level (e.g. "debug" to see per-file analysis).
    let tix_level = log_level_override.as_deref().unwrap_or("info");
    let default_filter =
        format!("warn,tix_lsp={tix_level},lang_check={tix_level},lang_ast={tix_level}");
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or(&default_filter))
        .init();

    log::info!(
        "tix lsp {} starting (pid {})",
        env!("CARGO_PKG_VERSION"),
        std::process::id(),
    );

    #[cfg(unix)]
    let rss_limit_mb = apply_limits(mem_limit_override);
    #[cfg(not(unix))]
    let rss_limit_mb: Option<f64> = {
        let _ = mem_limit_override;
        None
    };

    let mut registry = TypeAliasRegistry::with_builtins();

    // Allow overriding built-in context stubs via env var. When set, @nixos
    // and @home-manager resolve from this directory instead of the compiled-in
    // minimal stubs, enabling richer stubs with doc comments.
    if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
        log::info!("TIX_BUILTIN_STUBS override: {dir}");
        registry.set_builtin_stubs_dir(std::path::PathBuf::from(dir));
    }

    log::info!(
        "Initial registry: {} type aliases, {} global vals",
        registry.alias_count(),
        registry.global_vals().len(),
    );

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) =
        LspService::new(|client| server::TixLanguageServer::new(client, registry, rss_limit_mb));

    Server::new(stdin, stdout, socket).serve(service).await;
}

/// Detect total physical memory via sysconf. Returns MiB, or 0 on failure.
#[cfg(unix)]
fn total_memory_mib() -> u64 {
    // SAFETY: sysconf is a standard POSIX function with no unsafe preconditions.
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if pages <= 0 || page_size <= 0 {
        return 0;
    }
    (pages as u64 * page_size as u64) / (1024 * 1024)
}

/// Set RSS and RLIMIT_AS limits to prevent runaway memory usage.
///
/// The RSS limit is what actually gates inference — when process RSS exceeds
/// this, inference bails out with partial results. RLIMIT_AS is set to 2.5x
/// the RSS limit as a hard backstop for virtual address space.
///
/// Default RSS limit: 80% of system RAM (fallback: 3200 MiB if detection
/// fails). CLI `--mem-limit` / `TIX_MEM_LIMIT` override the RSS limit
/// directly (in MiB). Set to 0 to disable both limits.
///
/// Returns the effective RSS limit in MB (as f64), or `None` if disabled.
#[cfg(unix)]
fn apply_limits(cli_override: Option<u64>) -> Option<f64> {
    let total_mib = total_memory_mib();
    if total_mib > 0 {
        log::info!("Detected system memory: {} MiB", total_mib);
    }

    // 80% of system RAM, or 3200 MiB (80% of 4 GiB) if detection failed.
    let default_rss_mib: u64 = if total_mib > 0 {
        (total_mib as f64 * 0.8) as u64
    } else {
        3200
    };

    // CLI flag takes priority over env var.
    let rss_mib = if let Some(mib) = cli_override {
        if mib == 0 {
            log::info!("--mem-limit 0: memory limit disabled");
            return None;
        }
        mib
    } else {
        match std::env::var("TIX_MEM_LIMIT") {
            Ok(val) => match val.parse::<u64>() {
                Ok(0) => {
                    log::info!("TIX_MEM_LIMIT=0: memory limit disabled");
                    return None;
                }
                Ok(mib) => mib,
                Err(_) => {
                    log::warn!(
                        "Invalid TIX_MEM_LIMIT value '{val}', using default {default_rss_mib} MiB"
                    );
                    default_rss_mib
                }
            },
            Err(_) => default_rss_mib,
        }
    };

    log::info!("RSS limit for inference: {} MiB", rss_mib);

    // Set RLIMIT_AS to 2.5x the RSS limit as a hard backstop. Virtual address
    // space is typically 2-3x RSS due to allocator reservations, mmap regions,
    // shared libraries, etc.
    let rlimit_as_bytes = rss_mib as u128 * 1024 * 1024 * 5 / 2;
    // Cap at u64::MAX to avoid overflow in the rlimit API.
    let rlimit_as_bytes = rlimit_as_bytes.min(u64::MAX as u128) as u64;

    match Resource::AS.get() {
        Ok((_, hard)) => {
            let effective = if hard == rlimit::INFINITY {
                rlimit_as_bytes
            } else {
                rlimit_as_bytes.min(hard)
            };
            match Resource::AS.set(effective, hard) {
                Ok(()) => {
                    log::info!("RLIMIT_AS set to {} MiB", effective / (1024 * 1024));
                }
                Err(e) => {
                    log::warn!("Failed to set RLIMIT_AS: {e}");
                }
            }
        }
        Err(e) => {
            log::warn!("Failed to query RLIMIT_AS: {e}");
        }
    }

    Some(rss_mib as f64)
}
