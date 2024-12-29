use clap::Parser;
use lang::{Expr, lower::lower};
use std::error::Error;
use std::fs;
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

    // TODO: move this out of here so this crate doesn't need rnix as a dep
    let nix = rnix::Root::parse(&src).ok()?;

    let (module, _source_map) = lower(nix);

    // dbg!(module, source_map);

    dbg!(module);

    // for (id, expr) in module.iter_exprs() {
    //     if let Expr::Lambda { param, pat, body } = expr {
    //         if let Some(pat) = pat {
    //             dbg!(&pat.fields);
    //         }
    //     }
    // }

    // let root_expr = &module[module.entry_expr];
    // if let Expr::Lambda { param, pat, body } = root_expr {
    //     if let Some(pat) = pat {
    //         let (name, expr) = pat.fields[0];

    //         dbg!(&module[name.unwrap()]);

    //         dbg!(&module[expr.unwrap()]);
    //     }
    // }

    Ok(())
}
