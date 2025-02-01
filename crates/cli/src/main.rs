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

    dbg!(&module);

    let inference = dbg!(check_file(&db, file)?);

    let root_ty = inference
        .expr_ty_map
        .get(&module.entry_expr)
        .expect("No type for root module entry");

    dbg!(root_ty);

    Ok(())
}
