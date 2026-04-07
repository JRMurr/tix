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
