mod checker;
mod comment;
mod expr;
mod nix_file;

use std::error::Error;
use std::fs;

use clap::Parser;
use comment::get_expr_docs;
use expr::ExprTable;
use rnix::ast::HasEntry;

use rowan::ast::AstNode;

use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the file to read
    file_path: PathBuf,
}

fn collect_bindings(expr: rnix::ast::Expr) {
    match expr {
        rnix::ast::Expr::Apply(apply) => {
            if let Some(lambda) = apply.lambda() {
                // the function to be applied to, name or a anon function
                collect_bindings(lambda)
            }

            if let Some(argument) = apply.argument() {
                collect_bindings(argument)
            }
        }
        rnix::ast::Expr::Assert(_assert) => todo!(),
        rnix::ast::Expr::Error(_error) => todo!(),
        rnix::ast::Expr::IfElse(_if_else) => todo!(),
        rnix::ast::Expr::Select(_select) => {
            // this seems to be doing "lookup" aka doing a "." on an attr like
            // builtins.concatStringSep

            // TODO - do something?
        }
        rnix::ast::Expr::Str(_) => {
            // TODO - do something?
        }
        rnix::ast::Expr::Path(_path) => todo!(),
        rnix::ast::Expr::Literal(_literal) => {
            // TODO - do something?
        }
        rnix::ast::Expr::Lambda(lambda) => {
            // TODO: collect the function params as identifiers
            // if let Some(param) = lambda.param() {
            //     match param {
            //         Param::Pattern(pattern) => todo!(),
            //         Param::IdentParam(ident_param) => todo!(),
            //     }
            // }

            if let Some(body) = lambda.body() {
                collect_bindings(body)
            }
        }
        rnix::ast::Expr::LegacyLet(legacy_let) => todo!("legacy let not handled: {legacy_let}"),
        rnix::ast::Expr::LetIn(let_in) => {
            let s = let_in.syntax();
            dbg!(get_expr_docs(s));

            // these are the bindings used in the body
            for entry in let_in.entries() {
                match entry {
                    rnix::ast::Entry::Inherit(inherit) => {
                        todo!("inherit is not handled in let in: {inherit}");
                    }
                    rnix::ast::Entry::AttrpathValue(attrpath_value) => {
                        dbg!(attrpath_value.to_string());
                        if let Some(v) = attrpath_value.value() {
                            collect_bindings(v);
                        }
                    }
                }
            }

            if let Some(body) = let_in.body() {
                collect_bindings(body)
            }
        }
        rnix::ast::Expr::List(_list) => todo!(),
        rnix::ast::Expr::BinOp(bin_op) => {
            if let Some(lhs) = bin_op.lhs() {
                collect_bindings(lhs)
            }

            if let Some(rhs) = bin_op.rhs() {
                collect_bindings(rhs)
            }
        }
        rnix::ast::Expr::Paren(_paren) => todo!(),
        rnix::ast::Expr::Root(_root) => todo!(),
        rnix::ast::Expr::AttrSet(attr_set) => {
            // let s = attr_set.syntax();
            // dbg!(get_expr_docs(s));

            for entry in attr_set.entries() {
                match entry {
                    rnix::ast::Entry::Inherit(inherit) => {
                        dbg!(inherit.to_string());
                    }
                    rnix::ast::Entry::AttrpathValue(attrpath_value) => {
                        dbg!(attrpath_value.to_string());
                        if let Some(v) = attrpath_value.value() {
                            collect_bindings(v);
                        }
                    }
                }
            }
        }
        rnix::ast::Expr::UnaryOp(_unary_op) => todo!(),
        rnix::ast::Expr::Ident(_ident) => {
            // nothing
        }
        rnix::ast::Expr::With(_with) => todo!(),
        rnix::ast::Expr::HasAttr(_has_attr) => todo!(),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    let src = fs::read_to_string(&args.file_path)?;

    let nix = rnix::Root::parse(&src).ok()?;

    let expr = nix.expr().expect("not a valid expression");

    // dbg!(nix.expr());

    // collect_bindings(expr);

    let mut expr_table = ExprTable::new();

    let expr_id = expr_table.transform_ast(expr, None);

    dbg!(expr_id);

    Ok(())
}
