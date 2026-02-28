use std::path::PathBuf;

use clap::Parser;
use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::{LspService, Server};

use tix_lsp::{load_stubs, server};

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

fn main() {
    // Build a custom tokio runtime with 16MB worker thread stacks. The default
    // (~8MB on Linux) can overflow on deep import trees where file_root_type
    // recurses through many transitive imports, each allocating Module,
    // NameResolution, CheckCtx, etc. on the stack.
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(16 * 1024 * 1024)
        .build()
        .expect("failed to build tokio runtime");
    rt.block_on(async_main());
}

async fn async_main() {
    // Default to info-level for tix/lang crates, warn for everything else.
    // RUST_LOG env var overrides this if set.
    env_logger::Builder::from_env(
        env_logger::Env::default()
            .default_filter_or("warn,tix_lsp=info,lang_check=info,lang_ast=info"),
    )
    .init();

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
