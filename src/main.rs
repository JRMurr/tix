mod checker;
mod comment;
mod expr;
mod nix_file;

use std::error::Error;
use std::fs;

use clap::Parser;
use expr::ExprTable;

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

    let expr = nix.expr().expect("not a valid expression");

    // dbg!(nix.expr());

    let mut expr_table = ExprTable::new();

    let expr_id = expr_table.transform_ast(expr, None);

    dbg!(expr_table.get_expr(expr_id));

    Ok(())
}
