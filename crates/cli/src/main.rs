use std::{error::Error, path::PathBuf};

use clap::Parser;
use lang_ast::{module_and_source_maps, RootDatabase};
use lang_check::check_file;

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
    let mut seen = std::collections::BTreeMap::<String, String>::new();
    for (name_id, name) in module.names() {
        if let Some(ty) = inference.name_ty_map.get(&name_id) {
            let ty_str = ty.to_string();
            seen.entry(name.text.to_string())
                .and_modify(|existing| {
                    // Keep the more informative type (longer string, or non-tyvar).
                    if existing.len() < ty_str.len() {
                        *existing = ty_str.clone();
                    }
                })
                .or_insert(ty_str);
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
