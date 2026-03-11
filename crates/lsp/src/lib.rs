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
pub fn run_lsp() {
    // Build a custom tokio runtime with 16MB worker thread stacks. The default
    // (~8MB on Linux) can overflow on deep import trees where file_root_type
    // recurses through many transitive imports, each allocating Module,
    // NameResolution, CheckCtx, etc. on the stack.
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(16 * 1024 * 1024)
        .build()
        .expect("failed to build tokio runtime");
    rt.block_on(async_lsp_main());
}

async fn async_lsp_main() {
    // Default to info-level for tix/lang crates, warn for everything else.
    // RUST_LOG env var overrides this if set.
    env_logger::Builder::from_env(
        env_logger::Env::default()
            .default_filter_or("warn,tix_lsp=info,lang_check=info,lang_ast=info"),
    )
    .init();

    log::info!(
        "tix lsp {} starting (pid {})",
        env!("CARGO_PKG_VERSION"),
        std::process::id(),
    );

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
        LspService::new(|client| server::TixLanguageServer::new(client, registry));

    Server::new(stdin, stdout, socket).serve(service).await;
}
