use std::collections::HashMap;

use rnix::{
    ast::{self, AstToken},
    match_ast, NodeOrToken, Root, SyntaxNode, WalkEvent,
};
use rowan::ast::AstNode;

use crate::{AstPtr, DocComment, DocComments};

fn doc_text(comment: &rnix::ast::Comment) -> Option<DocComment> {
    let text = comment.syntax().text();
    // Block doc-comment: /** type: name :: Type */
    if text.starts_with(r#"/**"#) && comment.text().starts_with('*') {
        comment.text().strip_prefix('*').map(|x| x.into())
    // Line comment with type annotation: # type: name :: Type
    // rnix's Comment::text() strips the `#` prefix, so for `# type: pkgs :: Pkgs`
    // it returns ` type: pkgs :: Pkgs` — exactly what the pest grammar expects.
    } else if text.starts_with('#') {
        let trimmed = comment.text().trim_start();
        // Line comment with type annotation: # type: name :: Type
        // Line comment with inline type alias: # type Foo = ...;
        if trimmed.starts_with("type:")
            || (trimmed.starts_with("type ")
                && trimmed.as_bytes().get(5).is_some_and(|b| b.is_ascii_uppercase()))
        {
            Some(comment.text().into())
        } else {
            None
        }
    } else {
        None
    }
}

// Type alias doc comments (e.g. `/** type Foo = int; */` or `# type Foo = int;`)
// are recognized by doc_text() and collected during lowering into
// Module.inline_type_aliases. They may be orphan comments or attached to a
// nearby node — both cases are handled.
#[derive(Default, Debug)]
pub struct DocCommentCtx {
    /// For each node's pointer, store *all* doc comments that were associated with it.
    /// Sometimes people gather multiple lines of doc comments, or just a single.
    docs_for_node: HashMap<AstPtr, DocComments>,

    /// Comments that you couldn't attach to any particular node (e.g. file-level
    /// doc or trailing comments).
    pub(crate) orphan_docs: Vec<String>,
}

impl DocCommentCtx {
    pub fn get_docs(&self, ptr: &AstPtr) -> Option<&DocComments> {
        self.docs_for_node.get(ptr)
    }

    pub fn get_docs_for_syntax(&self, node: &SyntaxNode) -> Option<&DocComments> {
        let ptr = AstPtr::new(node);
        self.get_docs(&ptr)
    }
}

/// First pass: walk all tokens in the file, and figure out which doc comments
/// should be attached to which node.
pub fn gather_doc_comments(root: &Root) -> DocCommentCtx {
    let mut out = DocCommentCtx::default();

    let mut pending_doc_comments: Vec<String> = Vec::new();
    for event in root.syntax().preorder_with_tokens() {
        match event {
            WalkEvent::Enter(NodeOrToken::Token(ref token)) => {
                match_ast! { match token {
                        ast::Comment(it) => {
                            if let Some(text) = doc_text(&it) {
                                pending_doc_comments.push(text);
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
                        ast::PatEntry(e) => Some(AstPtr::new(e.syntax())),
                        // TODO: probably should handle inherit here as well
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
