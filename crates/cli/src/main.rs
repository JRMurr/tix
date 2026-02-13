use std::{error::Error, path::PathBuf};

use clap::Parser;
use lang_ast::{module_and_source_maps, RootDatabase};
use lang_check::check_file;
use lang_ty::OutputTy;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the file to read
    file_path: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    let db: RootDatabase = Default::default();

    let file = db.read_file(args.file_path)?;

    let (module, _source_map) = module_and_source_maps(&db, file);

    let inference = check_file(&db, file)?;

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
