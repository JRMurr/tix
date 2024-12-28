mod checker;
mod comment;
mod lang;
mod nix_file;

use std::error::Error;
use std::fs;

use clap::Parser;
// use lang::expr_table::ExprTable;
use lang::lower::lower;

use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the file to read
    file_path: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    let src = fs::read_to_string(&args.file_path)?;

    let nix = rnix::Root::parse(&src).ok()?;

    let (module, source_map) = lower(nix);

    dbg!(module, source_map);

    Ok(())
}
