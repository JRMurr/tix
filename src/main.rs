mod checker;
mod comment;
mod nix_file;

use std::error::Error;
use std::fs;

use clap::Parser;
use comment::get_expr_docs;
use rnix::ast::{Expr, HasEntry};

use rowan::ast::AstNode;

use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the file to read
    file_path: PathBuf,
}

// struct ExprType {
//     expr: Expr,
//     t: Option<String>, // TODO: real thing
// }

// fn collect_bindings(
//     node: &SyntaxNode,
//     // prefix: &str,
//     // category: &str,
//     // locs: &HashMap<String, String>,
//     // scope: HashMap<String, ManualEntry>,
// ) {
//     for ev in node.preorder() {
//         match ev {
//             WalkEvent::Enter(n) if n.kind() == SyntaxKind::NODE_ATTR_SET => {
//                 // let mut entries = vec![];
//                 for child in n.children() {
//                     if let Some(apv) = AttrpathValue::cast(child.clone()) {
//                         dbg!(apv);
//                         // entries.extend(
//                         //     collect_entry_information(apv)
//                         //         .map(|di| di.into_entry(prefix, category, locs)),
//                         // );
//                     } else if let Some(inh) = Inherit::cast(child) {
//                         // `inherit (x) ...` needs much more handling than we can
//                         // reasonably do here
//                         if inh.from().is_some() {
//                             continue;
//                         }

//                         for a in inh.attrs() {
//                             if let Attr::Ident(i) = a {
//                                 dbg!(i);
//                             }
//                         }
//                         // inh.attrs().filter_map(|a| match a {
//                         //     Attr::Ident(i) => {
//                         //         dbg!(a);
//                         //     }
//                         //     _ => (),
//                         // });
//                         // entries.extend(inh.attrs().filter_map(|a| match a {
//                         //     Attr::Ident(i) => scope.get(&i.syntax().text().to_string()).cloned(),
//                         //     // ignore non-ident keys. these aren't useful as lib
//                         //     // functions in general anyway.
//                         //     _ => None,
//                         // }));
//                     }
//                 }
//                 // return entries;
//             }
//             _ => (),
//         }
//     }
// }

// // prefix: &str, category: &str, locs: &HashMap<String, String>
// fn collect_entries(root: rnix::Root) {
//     let mut preorder = root.syntax().preorder();
//     while let Some(ev) = preorder.next() {
//         match ev {
//             // TODO: For now skip parsing the `{pkgs, ...}` at the top of the file
//             WalkEvent::Enter(n) if n.kind() == SyntaxKind::NODE_PATTERN => {
//                 preorder.skip_subtree();
//                 // dbg!(n);
//             }
//             WalkEvent::Enter(n) if n.kind() == SyntaxKind::NODE_LET_IN => {
//                 // dbg!(n);
//                 // collect_bindings(LetIn::cast(n.clone()).unwrap().body().unwrap().syntax());
//                 preorder.skip_subtree();
//             }
//             WalkEvent::Enter(n) if n.kind() == SyntaxKind::NODE_ATTR_SET => {
//                 // collect_bindings(&dbg!(n));
//                 // dbg!(n);
//                 preorder.skip_subtree();
//             }
//             WalkEvent::Enter(n) => {
//                 dbg!(n);
//             }
//             _ => (),
//         }
//     }
// }

fn collect_bindings(expr: Expr) {
    match expr {
        Expr::Apply(apply) => {
            if let Some(lambda) = apply.lambda() {
                // the function to be applied to
                collect_bindings(lambda)
            }

            if let Some(argument) = apply.argument() {
                collect_bindings(argument)
            }
        }
        Expr::Assert(_assert) => todo!(),
        Expr::Error(_error) => todo!(),
        Expr::IfElse(_if_else) => todo!(),
        Expr::Select(_select) => {
            // this seems to be doing "lookup" aka doing a "." on an attr like
            // builtins.concatStringSep

            // TODO - do something?
        }
        Expr::Str(_) => {
            // TODO - do something?
        }
        Expr::Path(_path) => todo!(),
        Expr::Literal(_literal) => {
            // TODO - do something?
        }
        Expr::Lambda(lambda) => {
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
        Expr::LegacyLet(legacy_let) => todo!("legacy let not handled: {legacy_let}"),
        Expr::LetIn(let_in) => {
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
        Expr::List(_list) => todo!(),
        Expr::BinOp(bin_op) => {
            if let Some(lhs) = bin_op.lhs() {
                collect_bindings(lhs)
            }

            if let Some(rhs) = bin_op.rhs() {
                collect_bindings(rhs)
            }
        }
        Expr::Paren(_paren) => todo!(),
        Expr::Root(_root) => todo!(),
        Expr::AttrSet(attr_set) => {
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
        Expr::UnaryOp(_unary_op) => todo!(),
        Expr::Ident(_ident) => {
            // nothing
        }
        Expr::With(_with) => todo!(),
        Expr::HasAttr(_has_attr) => todo!(),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    let src = fs::read_to_string(&args.file_path)?;

    let nix = rnix::Root::parse(&src).ok()?;

    let expr = nix.expr().expect("not a valid expression");

    // dbg!(nix.expr());

    collect_bindings(expr);

    Ok(())
}
