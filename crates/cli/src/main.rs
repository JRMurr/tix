mod config;
mod gen_stubs;

use std::collections::{HashMap, HashSet};
use std::{error::Error, path::PathBuf};

use clap::{Parser, Subcommand};
use lang_ast::{module_and_source_maps, name_resolution, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_file_collecting;
use lang_check::diagnostic::TixDiagnosticKind;
use lang_check::imports::resolve_imports;
use lang_ty::OutputTy;
use miette::{LabeledSpan, NamedSource};
use rowan::ast::AstNode;

// =============================================================================
// CLI Argument Parsing
// =============================================================================
//
// The CLI supports two modes:
//   1. Type-check mode (default): `tix-cli file.nix [--stubs ...]`
//   2. Subcommand mode: `tix-cli gen-stubs nixos [...]`
//
// Backward compatibility: bare `tix-cli file.nix` works because `file_path`
// is parsed when no subcommand matches.

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Path to the Nix file to type-check
    file_path: Option<PathBuf>,

    /// Paths to .tix stub files or directories (recursive)
    #[arg(long = "stubs", value_name = "PATH")]
    stub_paths: Vec<PathBuf>,

    /// Do not load the built-in nixpkgs stubs
    #[arg(long)]
    no_default_stubs: bool,

    /// Path to tix.toml config file (auto-discovered if not specified)
    #[arg(long = "config", value_name = "PATH")]
    config_path: Option<PathBuf>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Generate .tix stub files from external sources
    GenStubs {
        #[command(subcommand)]
        source: GenStubsSource,
    },
}

/// Shared CLI arguments for all gen-stubs subcommands.
#[derive(clap::Args, Debug)]
struct CommonGenStubsArgs {
    /// Path to nixpkgs (default: <nixpkgs> from NIX_PATH)
    #[arg(long)]
    nixpkgs: Option<PathBuf>,

    /// Path to a flake directory (evaluates configurations)
    #[arg(long)]
    flake: Option<PathBuf>,

    /// Read pre-computed option tree JSON instead of running nix eval
    #[arg(long)]
    from_json: Option<PathBuf>,

    /// Output file path (default: stdout)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Maximum depth for recursive option tree walking
    #[arg(long, default_value = "8")]
    max_depth: u32,

    /// Include option descriptions as ## doc comments in the output
    #[arg(long)]
    descriptions: bool,
}

impl From<CommonGenStubsArgs> for gen_stubs::CommonOptions {
    fn from(args: CommonGenStubsArgs) -> Self {
        Self {
            nixpkgs: args.nixpkgs,
            flake: args.flake,
            from_json: args.from_json,
            output: args.output,
            max_depth: args.max_depth,
            descriptions: args.descriptions,
        }
    }
}

#[derive(Subcommand, Debug)]
enum GenStubsSource {
    /// Generate stubs from NixOS option declarations
    Nixos {
        #[command(flatten)]
        common: CommonGenStubsArgs,

        /// Hostname to select from nixosConfigurations (required if flake has multiple)
        #[arg(long)]
        hostname: Option<String>,
    },

    /// Generate stubs from Home Manager option declarations
    HomeManager {
        #[command(flatten)]
        common: CommonGenStubsArgs,

        /// Path to home-manager source (default: flake registry)
        #[arg(long)]
        home_manager: Option<PathBuf>,

        /// Username to select from homeConfigurations (required if flake has multiple)
        #[arg(long)]
        username: Option<String>,
    },
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    match args.command {
        Some(Command::GenStubs { source }) => run_gen_stubs(source),
        None => {
            let file_path = args.file_path.ok_or(
                "No file path provided. Usage: tix-cli <file.nix> or tix-cli gen-stubs <source>",
            )?;
            run_check(
                file_path,
                args.stub_paths,
                args.no_default_stubs,
                args.config_path,
            )
        }
    }
}

// =============================================================================
// gen-stubs dispatch
// =============================================================================

fn run_gen_stubs(source: GenStubsSource) -> Result<(), Box<dyn Error>> {
    match source {
        GenStubsSource::Nixos { common, hostname } => {
            gen_stubs::run_nixos(gen_stubs::NixosOptions {
                common: common.into(),
                hostname,
            })
        }
        GenStubsSource::HomeManager {
            common,
            home_manager,
            username,
        } => gen_stubs::run_home_manager(gen_stubs::HomeManagerOptions {
            common: common.into(),
            home_manager,
            username,
        }),
    }
}

// =============================================================================
// Type-check mode (original behavior)
// =============================================================================

fn run_check(
    file_path: PathBuf,
    stub_paths: Vec<PathBuf>,
    no_default_stubs: bool,
    config_path: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    // Load .tix stub files into the type alias registry.
    // Built-in nixpkgs stubs are included by default unless --no-default-stubs is passed.
    let mut registry = if no_default_stubs {
        TypeAliasRegistry::new()
    } else {
        TypeAliasRegistry::with_builtins()
    };

    // Allow overriding built-in context stubs (e.g. @nixos, @home-manager) with
    // generated stubs from a directory. Used by the Nix `with-stubs` wrapper to
    // provide fully-typed NixosConfig/HomeManagerConfig instead of the minimal
    // compiled-in stubs.
    if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
        registry.set_builtin_stubs_dir(PathBuf::from(dir));
    }

    for stub_path in &stub_paths {
        load_stubs(&mut registry, stub_path)?;
    }

    // Discover or load tix.toml configuration.
    let canonical_path = std::fs::canonicalize(&file_path).unwrap_or(file_path.clone());
    let (toml_config, config_dir) = match &config_path {
        Some(explicit_path) => {
            let cfg = config::load_config(explicit_path)?;
            // Canonicalize the config directory so strip_prefix works against
            // the canonicalized file path (both must be absolute).
            let raw_dir = explicit_path.parent().unwrap_or(std::path::Path::new("."));
            let dir = std::fs::canonicalize(raw_dir).unwrap_or(raw_dir.to_path_buf());
            (Some(cfg), Some(dir))
        }
        None => {
            // Walk up from the file's parent directory looking for tix.toml.
            let start_dir = canonical_path.parent().unwrap_or(std::path::Path::new("."));
            match config::find_config(start_dir) {
                Some(found_config_path) => {
                    let dir = found_config_path
                        .parent()
                        .unwrap_or(std::path::Path::new("."))
                        .to_path_buf();
                    match config::load_config(&found_config_path) {
                        Ok(cfg) => (Some(cfg), Some(dir)),
                        Err(e) => {
                            eprintln!(
                                "Warning: failed to load {}: {e}",
                                found_config_path.display()
                            );
                            (None, None)
                        }
                    }
                }
                None => (None, None),
            }
        }
    };

    // Load additional stubs from tix.toml config.
    if let (Some(ref cfg), Some(ref dir)) = (&toml_config, &config_dir) {
        for stub in &cfg.stubs {
            let stub_path = dir.join(stub);
            if let Err(e) = load_stubs(&mut registry, &stub_path) {
                eprintln!(
                    "Warning: failed to load config stub '{}': {e}",
                    stub_path.display()
                );
            }
        }
    }

    if let Err(cycles) = registry.validate() {
        eprintln!("Error: cyclic type aliases detected: {:?}", cycles);
        std::process::exit(1);
    }

    // Resolve context args for this file based on tix.toml context definitions.
    let context_args = if let (Some(ref cfg), Some(ref dir)) = (&toml_config, &config_dir) {
        config::resolve_context_for_file(&canonical_path, cfg, dir, &mut registry).unwrap_or_else(
            |e| {
                eprintln!("Warning: failed to resolve context: {e}");
                HashMap::new()
            },
        )
    } else {
        HashMap::new()
    };

    let db: RootDatabase = Default::default();

    let file = db.read_file(file_path.clone())?;

    let (module, source_map) = module_and_source_maps(&db, file);
    let name_res = name_resolution(&db, file);

    // Resolve literal imports recursively before type-checking.
    let mut in_progress = HashSet::new();
    let mut cache = HashMap::new();
    let import_resolution = resolve_imports(
        &db,
        file,
        &module,
        &name_res,
        &registry,
        &mut in_progress,
        &mut cache,
    );
    for err in &import_resolution.errors {
        eprintln!("Import warning: {:?}", err.kind);
    }

    let result = check_file_collecting(&db, file, &registry, import_resolution.types, context_args);

    // Render diagnostics with miette for source context.
    let source_text = std::fs::read_to_string(&file_path)?;
    let filename = file_path.display().to_string();
    let root = rnix::Root::parse(&source_text).tree();
    let mut has_errors = false;

    for diag in &result.diagnostics {
        let is_warning = matches!(
            diag.kind,
            TixDiagnosticKind::UnresolvedName { .. }
                | TixDiagnosticKind::AnnotationArityMismatch { .. }

        );
        if !is_warning {
            has_errors = true;
        }

        // Resolve ExprId → source span via the ModuleSourceMap.
        let span = source_map.node_for_expr(diag.at_expr).map(|ptr| {
            let node = ptr.to_node(root.syntax());
            let range = node.text_range();
            let start: usize = range.start().into();
            let len: usize = range.len().into();
            (start, len)
        });

        // Build help text for MissingField suggestions.
        let help = match &diag.kind {
            TixDiagnosticKind::MissingField {
                suggestion: Some(s),
                ..
            } => Some(format!("did you mean `{s}`?")),
            _ => None,
        };

        let labels = span
            .map(|(offset, len)| vec![LabeledSpan::at(offset..offset + len, "here")])
            .unwrap_or_default();

        let mut builder = miette::MietteDiagnostic::new(diag.kind.to_string());
        if !labels.is_empty() {
            builder = builder.with_labels(labels);
        }
        if let Some(help_text) = help {
            builder = builder.with_help(help_text);
        }
        if is_warning {
            builder = builder.with_severity(miette::Severity::Warning);
        }

        let report = miette::Report::new(builder)
            .with_source_code(NamedSource::new(filename.clone(), source_text.clone()));
        eprintln!("{:?}", report);
    }

    if has_errors {
        std::process::exit(1);
    }

    // If inference succeeded, print binding types and root type.
    if let Some(inference) = &result.inference {
        // Print per-name types (the let-bindings, function params, etc.).
        // Deduplicate by name text since the same name can appear multiple times
        // (e.g. a lambda pattern field `config` and a return attrset key `config`).
        // Prefer definitions (PatField, Param, LetIn) over PlainAttrset keys,
        // then prefer types without unions/intersections (cleaner early-canonical form).
        let mut seen = std::collections::BTreeMap::<String, (lang_ast::NameKind, OutputTy)>::new();
        for (name_id, name) in module.names() {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                seen.entry(name.text.to_string())
                    .and_modify(|(existing_kind, existing_ty)| {
                        // Prefer definitions over plain attrset keys.
                        if !existing_kind.is_definition() && name.kind.is_definition() {
                            *existing_kind = name.kind;
                            *existing_ty = ty.clone();
                        } else if existing_kind.is_definition() && !name.kind.is_definition() {
                            // Keep the existing definition type.
                        } else if ty.contains_union_or_intersection()
                            && !existing_ty.contains_union_or_intersection()
                        {
                            // Keep the existing (cleaner) one.
                        } else if !ty.contains_union_or_intersection()
                            && existing_ty.contains_union_or_intersection()
                        {
                            *existing_kind = name.kind;
                            *existing_ty = ty.clone();
                        }
                    })
                    .or_insert((name.kind, ty.clone()));
            }
        }

        println!("Bindings:");
        for (name, (_kind, ty)) in &seen {
            println!("  {name} :: {ty}");
        }

        // Print the root expression type.
        let root_ty = inference
            .expr_ty_map
            .get(module.entry_expr)
            .expect("No type for root module entry");

        println!("\nRoot type:\n  {root_ty}");
    }

    Ok(())
}

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
fn load_stubs(registry: &mut TypeAliasRegistry, path: &PathBuf) -> Result<(), Box<dyn Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                load_stubs(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                load_single_stub(registry, &entry_path)?;
            }
        }
    } else {
        load_single_stub(registry, path)?;
    }
    Ok(())
}

fn load_single_stub(
    registry: &mut TypeAliasRegistry,
    path: &PathBuf,
) -> Result<(), Box<dyn Error>> {
    let source = std::fs::read_to_string(path)?;
    let file = comment_parser::parse_tix_file(&source)
        .map_err(|e| format!("Error parsing {}: {}", path.display(), e))?;
    registry.load_tix_file(&file);
    Ok(())
}
