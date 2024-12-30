use clap::Parser;
use lang::{Db, RootDatabase, infer_file_debug};
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

    dbg!(infer_file_debug(&db, file));

    // let (module, _source_map) = module_and_source_maps(&db, file);

    // // dbg!(module, source_map);

    // dbg!(module);

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
