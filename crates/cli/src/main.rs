use std::{error::Error, path::PathBuf};

use clap::Parser;
use lang_ast::{module_and_source_maps, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_file_with_aliases;
use lang_ty::OutputTy;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the Nix file to type-check
    file_path: PathBuf,

    /// Paths to .tix stub files or directories (recursive)
    #[arg(long = "stubs", value_name = "PATH")]
    stub_paths: Vec<PathBuf>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    // Load .tix stub files into the type alias registry.
    let mut registry = TypeAliasRegistry::new();
    for stub_path in &args.stub_paths {
        load_stubs(&mut registry, stub_path)?;
    }
    if let Err(cycles) = registry.validate() {
        eprintln!("Error: cyclic type aliases detected: {:?}", cycles);
        std::process::exit(1);
    }

    let db: RootDatabase = Default::default();

    let file = db.read_file(args.file_path)?;

    let (module, _source_map) = module_and_source_maps(&db, file);

    let inference = check_file_with_aliases(&db, file, &registry)?;

    // Print per-name types (the let-bindings, function params, etc.).
    // Deduplicate by (name_text, type_string) since the same name can appear
    // multiple times (e.g. a let-binding and an inherit reference).
    let mut seen = std::collections::BTreeMap::<String, OutputTy>::new();
    for (name_id, name) in module.names() {
        if let Some(ty) = inference.name_ty_map.get(&name_id) {
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
        .get(&module.entry_expr)
        .expect("No type for root module entry");

    println!("\nRoot type:\n  {root_ty}");

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

fn load_single_stub(registry: &mut TypeAliasRegistry, path: &PathBuf) -> Result<(), Box<dyn Error>> {
    let source = std::fs::read_to_string(path)?;
    let file = comment_parser::parse_tix_file(&source)
        .map_err(|e| format!("Error parsing {}: {}", path.display(), e))?;
    registry.load_tix_file(&file);
    Ok(())
}
