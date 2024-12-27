// this file is mostly taken from https://github.com/nix-community/nixdoc/blob/master/src/comment.rs

use rnix::ast::{self, AstToken};
use rnix::{SyntaxNode, match_ast};
use rowan::ast::AstNode;

fn doc_text(comment: &rnix::ast::Comment) -> Option<&str> {
    let text = comment.syntax().text();
    // Check whether this is a doc-comment
    if text.starts_with(r#"/**"#) && comment.text().starts_with('*') {
        comment.text().strip_prefix('*')
    } else {
        None
    }
}

/// Function retrieves a doc-comment from the [ast::Expr]
///
/// Returns an [Option<String>] of the first suitable doc-comment.
/// Returns [None] in case no suitable comment was found.
///
/// Doc-comments can appear in two places for any expression
///
/// ```nix
/// # (1) directly before the expression (anonymous)
/// /** Doc */
/// bar: bar;
///
/// # (2) when assigning a name.
/// {
///   /** Doc */
///   foo = bar: bar;
/// }
/// ```
///
/// If the doc-comment is not found in place (1) the search continues at place (2)
/// More precisely before the NODE_ATTRPATH_VALUE (ast)
/// If no doc-comment was found in place (1) or (2) this function returns None.
pub fn get_expr_docs(expr: &SyntaxNode) -> Option<String> {
    if let Some(doc) = get_doc_comment(expr) {
        // Found in place (1)
        doc_text(&doc).map(|v| v.to_owned())
    } else if let Some(ref parent) = expr.parent() {
        match_ast! {
            match parent {
                ast::AttrpathValue(_) => {
                    if let Some(doc_comment) = get_doc_comment(parent) {
                        doc_text(&doc_comment).map(|v| v.to_owned())
                    }else{
                        None
                    }
                },
                _ => {
                    // Yet unhandled ast-nodes
                    None
                }

            }
        }
    } else {
        // There is no parent;
        // No further places where a doc-comment could be.
        None
    }
}

/// Looks backwards from the given expression
/// Only whitespace or non-doc-comments are allowed in between an expression and the doc-comment.
/// Any other Node or Token stops the peek.
fn get_doc_comment(expr: &SyntaxNode) -> Option<rnix::ast::Comment> {
    let mut prev = expr.prev_sibling_or_token();
    loop {
        match prev {
            Some(rnix::NodeOrToken::Token(ref token)) => {
                match_ast! { match token {
                    ast::Whitespace(_) => {
                        prev = token.prev_sibling_or_token();
                    },
                    ast::Comment(it) => {
                        if doc_text(&it).is_some() {
                            break Some(it);
                        }else{
                            //Ignore non-doc comments.
                            prev = token.prev_sibling_or_token();
                        }
                    },
                    _ => {
                        break None;
                    }
                }}
            }
            _ => break None,
        };
    }
}
