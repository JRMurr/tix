mod completion;
mod config;
mod convert;
mod diagnostics;
mod document_highlight;
mod document_link;
mod document_symbol;
mod formatting;
mod goto_def;
mod hover;
mod inlay_hint;
pub(crate) mod project_config;
mod references;
mod rename;
mod selection_range;
mod semantic_tokens;
mod server;
mod state;
#[cfg(test)]
mod test_util;
mod ty_nav;

use std::path::PathBuf;

use clap::Parser;
use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::{LspService, Server};

#[derive(Parser, Debug)]
#[command(author, version, about = "Tix Language Server")]
struct Cli {
    /// Paths to .tix stub files or directories (recursive)
    #[arg(long = "stubs", value_name = "PATH")]
    stub_paths: Vec<PathBuf>,

    /// Do not load the built-in nixpkgs stubs
    #[arg(long)]
    no_default_stubs: bool,
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let args = Cli::parse();

    log::info!(
        "tix-lsp {} starting (pid {})",
        env!("CARGO_PKG_VERSION"),
        std::process::id(),
    );

    // Load .tix stub files once at startup.
    // Built-in nixpkgs stubs are included by default unless --no-default-stubs is passed.
    let mut registry = if args.no_default_stubs {
        log::info!("Built-in stubs: disabled (--no-default-stubs)");
        TypeAliasRegistry::new()
    } else {
        log::info!("Built-in stubs: enabled");
        TypeAliasRegistry::with_builtins()
    };

    // Allow overriding built-in context stubs via env var. When set, @nixos
    // and @home-manager resolve from this directory instead of the compiled-in
    // minimal stubs, enabling richer stubs with doc comments.
    if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
        log::info!("TIX_BUILTIN_STUBS override: {dir}");
        registry.set_builtin_stubs_dir(PathBuf::from(dir));
    }

    for stub_path in &args.stub_paths {
        match load_stubs(&mut registry, stub_path) {
            Ok(()) => log::info!("Loaded CLI stubs from {}", stub_path.display()),
            Err(e) => log::warn!("Failed to load stubs from {}: {e}", stub_path.display()),
        }
    }
    if let Err(cycles) = registry.validate() {
        log::warn!("Cyclic type aliases detected: {:?}", cycles);
    }

    log::info!(
        "Initial registry: {} type aliases, {} global vals",
        registry.alias_count(),
        registry.global_vals().len(),
    );

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let cli_stub_paths = args.stub_paths;
    let no_default_stubs = args.no_default_stubs;

    let (service, socket) = LspService::new(|client| {
        server::TixLanguageServer::new(client, registry, cli_stub_paths, no_default_stubs)
    });

    Server::new(stdin, stdout, socket).serve(service).await;
}

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
pub(crate) fn load_stubs(
    registry: &mut TypeAliasRegistry,
    path: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                load_stubs(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                let source = std::fs::read_to_string(&entry_path)?;
                let file = comment_parser::parse_tix_file(&source)
                    .map_err(|e| format!("Error parsing {}: {e}", entry_path.display()))?;
                registry.load_tix_file(&file);
            }
        }
    } else {
        let source = std::fs::read_to_string(path)?;
        let file = comment_parser::parse_tix_file(&source)
            .map_err(|e| format!("Error parsing {}: {e}", path.display()))?;
        registry.load_tix_file(&file);
    }
    Ok(())
}
