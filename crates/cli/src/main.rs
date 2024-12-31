use clap::Parser;
use lang::{Db, RootDatabase};
use std::error::Error;
use std::path::PathBuf;

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

    dbg!(lang::infer_file_debug(&db, file));

    // let (module, _source_map) = lang::module_and_source_maps(&db, file);

    // dbg!(module);

    Ok(())
}
