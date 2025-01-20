use std::collections::HashMap;

use rnix::{
    NodeOrToken, Root, WalkEvent,
    ast::{self, AstToken},
    match_ast,
};
use rowan::ast::AstNode;

use crate::AstPtr;

fn doc_text(comment: &rnix::ast::Comment) -> Option<&str> {
    let text = comment.syntax().text();
    // Check whether this is a doc-comment
    if text.starts_with(r#"/**"#) && comment.text().starts_with('*') {
        comment.text().strip_prefix('*')
    } else {
        None
    }
}

// TODO: need a good way to handle doc comments that are just type aliases
// they don't need to be associated to a node and can just "hang" out.
// Parsing the doc comments could figure out if its just type aliases and handle it there?
#[derive(Default, Debug)]
pub struct DocComments {
    /// For each node's pointer, store *all* doc comments that were associated with it.
    /// Sometimes people gather multiple lines of doc comments, or just a single.
    pub docs_for_node: HashMap<AstPtr, Vec<String>>,

    /// Comments that you couldn't attach to any particular node (e.g. file-level
    /// doc or trailing comments).
    pub orphan_docs: Vec<String>,
}

/// First pass: walk all tokens in the file, and figure out which doc comments
/// should be attached to which node.
pub fn gather_doc_comments(root: &Root) -> DocComments {
    let mut out = DocComments::default();

    let mut pending_doc_comments: Vec<String> = Vec::new();
    for event in root.syntax().preorder_with_tokens() {
        match event {
            WalkEvent::Enter(NodeOrToken::Token(ref token)) => {
                match_ast! { match token {
                        ast::Comment(it) => {
                            if let Some(text) = doc_text(&it) {
                                pending_doc_comments.push(text.to_string());
                            }
                        },
                        _ => {}
                    }
                }
            }
            WalkEvent::Enter(NodeOrToken::Node(node)) => {
                if pending_doc_comments.is_empty() {
                    continue;
                }

                let ptr = match_ast! {
                    match node {
                        ast::Expr(e) => Some(AstPtr::new(e.syntax())),
                        ast::AttrpathValue(e) => Some(AstPtr::new(e.syntax())),
                        _ => None,
                    }
                };

                if let Some(ptr) = ptr {
                    out.docs_for_node
                        .entry(ptr)
                        .or_default()
                        .append(&mut pending_doc_comments);
                }
            }
            WalkEvent::Leave(_) => {}
        }
    }

    // If there are doc comments left unassigned (e.g. they were trailing at the end
    // of the file, or no node follows them), throw them into orphan docs
    if !pending_doc_comments.is_empty() {
        out.orphan_docs.append(&mut pending_doc_comments);
    }

    out
}
