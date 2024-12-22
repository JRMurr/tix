use std::fs;
use std::{collections::HashMap, error::Error};

use clap::Parser;
use rnix::{
    SyntaxKind, SyntaxNode,
    ast::{Attr, AttrpathValue, Expr, Inherit, LetIn},
};
use rowan::{WalkEvent, ast::AstNode};

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
        Expr::Apply(apply) => todo!(),
        Expr::Assert(assert) => todo!(),
        Expr::Error(error) => todo!(),
        Expr::IfElse(if_else) => todo!(),
        Expr::Select(select) => todo!(),
        Expr::Str(_) => todo!(),
        Expr::Path(path) => todo!(),
        Expr::Literal(literal) => todo!(),
        Expr::Lambda(lambda) => todo!(),
        Expr::LegacyLet(legacy_let) => todo!(),
        Expr::LetIn(let_in) => todo!(),
        Expr::List(list) => todo!(),
        Expr::BinOp(bin_op) => todo!(),
        Expr::Paren(paren) => todo!(),
        Expr::Root(root) => todo!(),
        Expr::AttrSet(attr_set) => todo!(),
        Expr::UnaryOp(unary_op) => todo!(),
        Expr::Ident(ident) => todo!(),
        Expr::With(with) => todo!(),
        Expr::HasAttr(has_attr) => todo!(),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    let src = fs::read_to_string(&args.file_path)?;

    let nix = rnix::Root::parse(&src).ok()?;

    let expr = nix.expr().expect("not a valid expression");

    // dbg!(nix.expr());

    collect_bindings(dbg!(expr));

    Ok(())
}
