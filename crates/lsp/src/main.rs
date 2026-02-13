mod completion;
mod convert;
mod diagnostics;
mod goto_def;
mod hover;
mod server;
mod state;

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
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let args = Cli::parse();

    // Load .tix stub files once at startup.
    let mut registry = TypeAliasRegistry::new();
    for stub_path in &args.stub_paths {
        if let Err(e) = load_stubs(&mut registry, stub_path) {
            eprintln!(
                "Warning: failed to load stubs from {}: {e}",
                stub_path.display()
            );
        }
    }
    if let Err(cycles) = registry.validate() {
        eprintln!("Warning: cyclic type aliases detected: {:?}", cycles);
    }

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) =
        LspService::new(|client| server::TixLanguageServer::new(client, registry));

    Server::new(stdin, stdout, socket).serve(service).await;
}

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
fn load_stubs(
    registry: &mut TypeAliasRegistry,
    path: &PathBuf,
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
