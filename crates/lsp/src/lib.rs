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
pub mod test_util;
mod ty_nav;
mod type_def;
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
    let mem_limit_mib = apply_mem_limit(mem_limit_override);
    #[cfg(not(unix))]
    let mem_limit_mib: Option<u64> = {
        let _ = mem_limit_override;
        None
    };

    // Compute RSS limit for inference. Virtual address space (RLIMIT_AS) is
    // typically 2-3x RSS due to allocator reservations, mmap regions, shared
    // libraries, etc. Using 40% of the virtual limit as an RSS threshold
    // prevents OOM crashes while leaving enough headroom for normal files.
    let rss_limit_mb = mem_limit_mib.map(|mib| mib as f64 * 0.4);
    if let Some(limit) = rss_limit_mb {
        log::info!("RSS limit for inference: {:.0} MB", limit);
    }

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

/// Apply a virtual address space limit via setrlimit(RLIMIT_AS) to prevent
/// runaway memory usage from taking down the user's system. CLI `--mem-limit`
/// flag takes priority, then `TIX_MEM_LIMIT` env var, then defaults to
/// 4096 MiB (4 GiB). Set to 0 to disable.
///
/// Returns the effective limit in MiB, or `None` if the limit was disabled
/// or could not be applied.
#[cfg(unix)]
fn apply_mem_limit(cli_override: Option<u64>) -> Option<u64> {
    const DEFAULT_MIB: u64 = 4096;

    // CLI flag takes priority over env var.
    let limit_mib = if let Some(mib) = cli_override {
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
                        "Invalid TIX_MEM_LIMIT value '{val}', using default {DEFAULT_MIB} MiB"
                    );
                    DEFAULT_MIB
                }
            },
            Err(_) => DEFAULT_MIB,
        }
    };

    let limit_bytes = limit_mib * 1024 * 1024;

    // Read the current hard limit so we don't try to exceed it (requires root).
    let hard = match Resource::AS.get() {
        Ok((_, hard)) => hard,
        Err(e) => {
            log::warn!("Failed to query RLIMIT_AS: {e}");
            return None;
        }
    };

    let effective = if hard == rlimit::INFINITY {
        limit_bytes
    } else {
        limit_bytes.min(hard)
    };

    match Resource::AS.set(effective, hard) {
        Ok(()) => {
            let effective_mib = effective / (1024 * 1024);
            log::info!("Memory limit set to {} MiB", effective_mib);
            Some(effective_mib)
        }
        Err(e) => {
            log::warn!("Failed to set memory limit to {limit_mib} MiB: {e}");
            None
        }
    }
}
