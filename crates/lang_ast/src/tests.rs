use std::collections::HashMap;
use std::path::PathBuf;

use crate::{ExprId, NameId, SyntaxResult};

// ==============================================================================
// Shared test helpers
// ==============================================================================

/// Find a NameId by its text. Panics if not found.
pub fn find_name(module: &crate::Module, text: &str) -> NameId {
    module
        .names()
        .find(|(_, n)| n.text == text)
        .unwrap_or_else(|| panic!("name {text:?} not found"))
        .0
}

/// Find the ExprId of the first `Expr::Reference` whose name string
/// matches `text`.
pub fn find_ref_expr(module: &crate::Module, text: &str) -> ExprId {
    module
        .exprs()
        .find(|(_, e)| matches!(e, crate::Expr::Reference(n) if n == text))
        .unwrap_or_else(|| panic!("reference to {text:?} not found"))
        .0
}

/// Find the first `IfThenElse` expression and return its condition ExprId.
pub fn find_if_condition(module: &crate::Module) -> ExprId {
    module
        .exprs()
        .find_map(|(_, e)| match e {
            crate::Expr::IfThenElse { cond, .. } => Some(*cond),
            _ => None,
        })
        .expect("no if-then-else found in module")
}

/// Find the first `Apply` expression and return its ExprId.
pub fn find_apply(module: &crate::Module) -> ExprId {
    module
        .exprs()
        .find_map(|(id, e)| match e {
            crate::Expr::Apply { .. } => Some(id),
            _ => None,
        })
        .expect("no Apply found in module")
}

/// Parse a single Nix source string through the full syntax pipeline.
pub fn parse_fixture(src: &str) -> SyntaxResult {
    crate::run_syntax_pipeline(src)
}

/// Parse multiple files and return a map of path → SyntaxResult.
/// The first file is treated as the entry point and also returned separately.
pub fn parse_multi_file(
    sources: &[(&str, &str)],
) -> (SyntaxResult, HashMap<PathBuf, SyntaxResult>) {
    let mut map = HashMap::new();
    let mut entry = None;
    for (i, &(path_str, contents)) in sources.iter().enumerate() {
        let result = crate::run_syntax_pipeline(contents);
        if i == 0 {
            entry = Some(result.clone());
        }
        map.insert(PathBuf::from(path_str), result);
    }
    (entry.expect("at least one file required"), map)
}

#[cfg(test)]
mod recursion_guard_tests {
    // Depth is capped at 15k: rowan's green-tree Drop recurses without a
    // guard and overflows around ~25k nesting on an 8MB stack. Our own
    // (guarded) walks have much larger frames, so 15k is still deep enough
    // to overflow without the stacker guards.

    /// Deep left-leaning binop chain: rnix parses it iteratively, but
    /// lowering and name resolution recurse down the left spine. Without
    /// stacker guards this overflows the stack.
    #[test]
    fn deep_binop_chain_no_overflow() {
        let src = format!("let x = 1; in x{}", " + x".repeat(15_000));
        let r = crate::run_syntax_pipeline(&src);
        assert!(r.module.exprs().count() > 15_000);
    }

    /// Deep `&&` chain as an if-condition: narrowing analysis recurses
    /// through the condition tree.
    #[test]
    fn deep_narrow_condition_no_overflow() {
        let src = format!(
            "let a = true; in if a{} then 1 else 2",
            " && a".repeat(15_000)
        );
        let r = crate::run_syntax_pipeline(&src);
        assert!(r.module.exprs().count() > 15_000);
    }
}
