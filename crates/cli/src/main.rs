mod config;

use std::collections::{HashMap, HashSet};
use std::{error::Error, path::PathBuf};

use clap::Parser;
use lang_ast::{module_and_source_maps, name_resolution, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_file_collecting;
use lang_check::diagnostic::TixDiagnosticKind;
use lang_check::imports::resolve_imports;
use lang_ty::OutputTy;
use miette::{LabeledSpan, NamedSource};
use rowan::ast::AstNode;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the Nix file to type-check
    file_path: PathBuf,

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

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    // Load .tix stub files into the type alias registry.
    // Built-in nixpkgs stubs are included by default unless --no-default-stubs is passed.
    let mut registry = if args.no_default_stubs {
        TypeAliasRegistry::new()
    } else {
        TypeAliasRegistry::with_builtins()
    };
    for stub_path in &args.stub_paths {
        load_stubs(&mut registry, stub_path)?;
    }

    // Discover or load tix.toml configuration.
    let file_path = std::fs::canonicalize(&args.file_path).unwrap_or(args.file_path.clone());
    let (toml_config, config_dir) = match &args.config_path {
        Some(explicit_path) => {
            let cfg = config::load_config(explicit_path)?;
            let dir = explicit_path
                .parent()
                .unwrap_or(std::path::Path::new("."))
                .to_path_buf();
            (Some(cfg), Some(dir))
        }
        None => {
            // Walk up from the file's parent directory looking for tix.toml.
            let start_dir = file_path.parent().unwrap_or(std::path::Path::new("."));
            match config::find_config(start_dir) {
                Some(config_path) => {
                    let dir = config_path
                        .parent()
                        .unwrap_or(std::path::Path::new("."))
                        .to_path_buf();
                    match config::load_config(&config_path) {
                        Ok(cfg) => (Some(cfg), Some(dir)),
                        Err(e) => {
                            eprintln!("Warning: failed to load {}: {e}", config_path.display());
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
        config::resolve_context_for_file(&file_path, cfg, dir, &mut registry).unwrap_or_else(|e| {
            eprintln!("Warning: failed to resolve context: {e}");
            HashMap::new()
        })
    } else {
        HashMap::new()
    };

    let db: RootDatabase = Default::default();

    let file = db.read_file(args.file_path.clone())?;

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
    let source_text = std::fs::read_to_string(&args.file_path)?;
    let filename = args.file_path.display().to_string();
    let root = rnix::Root::parse(&source_text).tree();
    let mut has_errors = false;

    for diag in &result.diagnostics {
        let is_warning = matches!(diag.kind, TixDiagnosticKind::UnresolvedName { .. });
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
        // Deduplicate by (name_text, type_string) since the same name can appear
        // multiple times (e.g. a let-binding and an inherit reference).
        let mut seen = std::collections::BTreeMap::<String, OutputTy>::new();
        for (name_id, name) in module.names() {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                seen.entry(name.text.to_string())
                    .and_modify(|existing| {
                        // When the same name appears multiple times (e.g. a let-binding
                        // and an inherit reference), prefer the version with fewer
                        // unions/intersections — that's the cleaner (early-canonicalized)
                        // form, not contaminated by use-site extrusion.
                        if ty.contains_union_or_intersection()
                            && !existing.contains_union_or_intersection()
                        {
                            // Keep the existing (cleaner) one.
                        } else if !ty.contains_union_or_intersection()
                            && existing.contains_union_or_intersection()
                        {
                            *existing = ty.clone();
                        }
                        // If both have or both lack unions/intersections, keep existing.
                    })
                    .or_insert(ty.clone());
            }
        }

        println!("Bindings:");
        for (name, ty) in &seen {
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
