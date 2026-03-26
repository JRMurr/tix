use std::collections::{HashMap, HashSet};

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
                && trimmed
                    .as_bytes()
                    .get(5)
                    .is_some_and(|b| b.is_ascii_uppercase()))
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

// ==============================================================================
// Suppression Directives
// ==============================================================================
//
// `# tix-nocheck` — suppress all diagnostics for the entire file.
// `# tix-ignore`  — suppress diagnostics on the next line.

/// Convert a byte offset to a 0-indexed line number.
pub fn line_of_offset(source: &str, byte_offset: usize) -> u32 {
    source[..byte_offset.min(source.len())]
        .bytes()
        .filter(|&b| b == b'\n')
        .count() as u32
}

/// Returns `true` if the file contains a `# tix-nocheck` comment anywhere.
pub fn has_nocheck_directive(root: &Root) -> bool {
    for event in root.syntax().preorder_with_tokens() {
        if let WalkEvent::Enter(NodeOrToken::Token(ref token)) = event {
            match_ast! { match token {
                ast::Comment(it) => {
                    let trimmed = it.text().trim();
                    if trimmed == "tix-nocheck" {
                        return true;
                    }
                },
                _ => {}
            }}
        }
    }
    false
}

/// Collect 0-indexed line numbers whose diagnostics should be suppressed.
///
/// For each `# tix-ignore` comment on line N, the *next* line (N+1) is added
/// to the returned set.
pub fn gather_ignore_lines(root: &Root, source: &str) -> HashSet<u32> {
    let mut ignored = HashSet::new();
    for event in root.syntax().preorder_with_tokens() {
        if let WalkEvent::Enter(NodeOrToken::Token(ref token)) = event {
            match_ast! { match token {
                ast::Comment(it) => {
                    let trimmed = it.text().trim();
                    if trimmed == "tix-ignore" {
                        let offset: usize = it.syntax().text_range().start().into();
                        let line = line_of_offset(source, offset);
                        ignored.insert(line + 1);
                    }
                },
                _ => {}
            }}
        }
    }
    ignored
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> Root {
        rnix::Root::parse(src).tree()
    }

    // =========================================================================
    // tix-nocheck
    // =========================================================================

    #[test]
    fn nocheck_detected_at_top() {
        let root = parse("# tix-nocheck\n42");
        assert!(has_nocheck_directive(&root));
    }

    #[test]
    fn nocheck_detected_in_middle() {
        let root = parse("let x = 1;\n# tix-nocheck\nin x");
        assert!(has_nocheck_directive(&root));
    }

    #[test]
    fn nocheck_not_present() {
        let root = parse("let x = 1; in x");
        assert!(!has_nocheck_directive(&root));
    }

    #[test]
    fn nocheck_not_triggered_by_partial_match() {
        // "tix-nocheck-extra" should not match
        let root = parse("# tix-nocheck-extra\n42");
        assert!(!has_nocheck_directive(&root));
    }

    #[test]
    fn nocheck_with_extra_whitespace() {
        let root = parse("#   tix-nocheck  \n42");
        assert!(has_nocheck_directive(&root));
    }

    // =========================================================================
    // tix-ignore
    // =========================================================================

    #[test]
    fn ignore_collects_next_line() {
        let src = "# tix-ignore\n1 + \"a\"\n";
        let root = parse(src);
        let lines = gather_ignore_lines(&root, src);
        assert_eq!(lines, HashSet::from([1]));
    }

    #[test]
    fn ignore_multiple_lines() {
        let src = "# tix-ignore\nfoo\nbar\n# tix-ignore\nbaz\n";
        let root = parse(src);
        let lines = gather_ignore_lines(&root, src);
        assert_eq!(lines, HashSet::from([1, 4]));
    }

    #[test]
    fn ignore_empty_when_no_directives() {
        let src = "let x = 1; in x";
        let root = parse(src);
        let lines = gather_ignore_lines(&root, src);
        assert!(lines.is_empty());
    }

    #[test]
    fn ignore_not_triggered_by_partial_match() {
        let src = "# tix-ignore-all\nfoo\n";
        let root = parse(src);
        let lines = gather_ignore_lines(&root, src);
        assert!(lines.is_empty());
    }

    #[test]
    fn ignore_with_extra_whitespace() {
        let src = "#   tix-ignore  \nfoo\n";
        let root = parse(src);
        let lines = gather_ignore_lines(&root, src);
        assert_eq!(lines, HashSet::from([1]));
    }

    // =========================================================================
    // line_of_offset
    // =========================================================================

    #[test]
    fn line_of_offset_first_line() {
        assert_eq!(line_of_offset("hello\nworld", 3), 0);
    }

    #[test]
    fn line_of_offset_second_line() {
        assert_eq!(line_of_offset("hello\nworld", 6), 1);
    }

    #[test]
    fn line_of_offset_at_newline() {
        assert_eq!(line_of_offset("hello\nworld", 5), 0);
    }
}
