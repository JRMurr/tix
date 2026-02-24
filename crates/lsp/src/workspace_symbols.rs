// ==============================================================================
// workspace/symbol — search for symbols across all analyzed files
// ==============================================================================
//
// Aggregates document symbols from every open/analyzed file and returns those
// whose names match the query string. The LSP spec says `workspace/symbol`
// returns flat `SymbolInformation` items (not nested `DocumentSymbol`), so we
// flatten the per-file hierarchical symbols and attach file URIs.
//
// Matching uses case-insensitive substring by default, with a bonus for prefix
// matches. This provides a practical "fuzzy enough" experience without pulling
// in a fuzzy-matching crate.

use tower_lsp::lsp_types::{DocumentSymbol, Location, SymbolInformation, Url};

use crate::state::AnalysisState;

/// Maximum number of results to return. Prevents flooding the editor with
/// thousands of symbols when the query is short or empty.
const MAX_RESULTS: usize = 200;

/// Collect workspace symbols matching `query` from all analyzed files.
///
/// An empty query returns all symbols (up to `MAX_RESULTS`). Non-empty queries
/// filter by case-insensitive substring match, with results sorted so that
/// prefix matches come first.
#[allow(deprecated)] // SymbolInformation.deprecated field is deprecated but required
pub fn workspace_symbols(state: &AnalysisState, query: &str) -> Vec<SymbolInformation> {
    let query_lower = query.to_lowercase();

    let mut results: Vec<(SymbolInformation, MatchQuality)> = Vec::new();

    for (path, analysis) in &state.files {
        let uri = match Url::from_file_path(path) {
            Ok(u) => u,
            Err(()) => continue,
        };

        let root = analysis.parsed.tree();
        let doc_symbols = crate::document_symbol::document_symbols(analysis, &root);

        // Flatten the hierarchical DocumentSymbol tree into workspace-level
        // SymbolInformation entries, filtering by name as we go.
        flatten_and_filter(
            &doc_symbols,
            &uri,
            &query_lower,
            None, // no container for top-level symbols
            &mut results,
        );
    }

    // Sort: exact matches first, then prefix matches, then substring matches.
    // Within each quality tier, sort alphabetically by name for stability.
    results.sort_by(|(a, qa), (b, qb)| qa.cmp(qb).then_with(|| a.name.cmp(&b.name)));

    results
        .into_iter()
        .take(MAX_RESULTS)
        .map(|(sym, _)| sym)
        .collect()
}

/// How well a symbol name matches the query, used for sorting results.
/// Lower values sort first (better match).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum MatchQuality {
    /// Name equals the query exactly (case-insensitive).
    Exact,
    /// Name starts with the query (case-insensitive).
    Prefix,
    /// Name contains the query as a substring (case-insensitive).
    Substring,
}

/// Determine how well `name_lower` matches `query_lower`.
/// Returns `None` if the name doesn't match at all.
fn match_quality(name_lower: &str, query_lower: &str) -> Option<MatchQuality> {
    if query_lower.is_empty() {
        // Empty query matches everything; treat as substring quality so
        // sorting is stable (all symbols are "equally matched").
        return Some(MatchQuality::Substring);
    }
    if name_lower == query_lower {
        Some(MatchQuality::Exact)
    } else if name_lower.starts_with(query_lower) {
        Some(MatchQuality::Prefix)
    } else if name_lower.contains(query_lower) {
        Some(MatchQuality::Substring)
    } else {
        None
    }
}

/// Recursively flatten `DocumentSymbol` children into `SymbolInformation`,
/// filtering by name match against `query_lower`.
#[allow(deprecated)] // SymbolInformation.deprecated field
fn flatten_and_filter(
    symbols: &[DocumentSymbol],
    uri: &Url,
    query_lower: &str,
    container_name: Option<&str>,
    out: &mut Vec<(SymbolInformation, MatchQuality)>,
) {
    for sym in symbols {
        let name_lower = sym.name.to_lowercase();

        if let Some(quality) = match_quality(&name_lower, query_lower) {
            out.push((
                SymbolInformation {
                    name: sym.name.clone(),
                    kind: sym.kind,
                    tags: sym.tags.clone(),
                    deprecated: None,
                    location: Location {
                        uri: uri.clone(),
                        range: sym.selection_range,
                    },
                    container_name: container_name.map(String::from),
                },
                quality,
            ));
        }

        // Recurse into children regardless of whether the parent matched,
        // because a child name might match even if the parent doesn't.
        if let Some(ref children) = sym.children {
            flatten_and_filter(children, uri, query_lower, Some(&sym.name), out);
        }
    }
}

/// Convenience wrapper for use from `server.rs` — calls `workspace_symbols`
/// with the locked state. Separated so the handler can remain thin.
pub fn handle_workspace_symbols(
    state: &AnalysisState,
    query: &str,
) -> Option<Vec<SymbolInformation>> {
    let results = workspace_symbols(state, query);
    Some(results)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::temp_path;
    use lang_check::aliases::TypeAliasRegistry;
    use tower_lsp::lsp_types::SymbolKind;

    use crate::state::AnalysisState;

    /// Helper: create an AnalysisState with multiple files and query workspace symbols.
    fn query_workspace(files: &[(&str, &str)], query: &str) -> Vec<SymbolInformation> {
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        for (name, src) in files {
            let path = temp_path(name);
            state.update_file(path, src.to_string());
        }
        workspace_symbols(&state, query)
    }

    #[test]
    fn empty_query_returns_all_symbols() {
        let results = query_workspace(
            &[("a.nix", "let x = 1; y = 2; in x")],
            "",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"x"), "should contain x, got: {names:?}");
        assert!(names.contains(&"y"), "should contain y, got: {names:?}");
    }

    #[test]
    fn filters_by_substring() {
        let results = query_workspace(
            &[("a.nix", "let fooBar = 1; bazQux = 2; in fooBar")],
            "bar",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        assert!(
            names.contains(&"fooBar"),
            "fooBar should match 'bar' substring, got: {names:?}"
        );
        assert!(
            !names.contains(&"bazQux"),
            "bazQux should not match 'bar', got: {names:?}"
        );
    }

    #[test]
    fn case_insensitive_match() {
        let results = query_workspace(
            &[("a.nix", "let MyFunc = x: x; in MyFunc")],
            "myfunc",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        assert!(
            names.contains(&"MyFunc"),
            "case-insensitive match should find MyFunc, got: {names:?}"
        );
    }

    #[test]
    fn aggregates_across_files() {
        let results = query_workspace(
            &[
                ("a.nix", "let alpha = 1; in alpha"),
                ("b.nix", "let bravo = 2; in bravo"),
            ],
            "",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"alpha"), "should contain alpha from a.nix");
        assert!(names.contains(&"bravo"), "should contain bravo from b.nix");
    }

    #[test]
    fn exact_match_sorts_before_prefix() {
        let results = query_workspace(
            &[("a.nix", "let id = 1; identity = 2; in id")],
            "id",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        // "id" is an exact match; "identity" is a prefix match.
        // Exact should come first.
        let id_pos = names.iter().position(|n| *n == "id");
        let identity_pos = names.iter().position(|n| *n == "identity");
        assert!(
            id_pos < identity_pos,
            "exact match 'id' should come before prefix match 'identity', got: {names:?}"
        );
    }

    #[test]
    fn prefix_match_sorts_before_substring() {
        let results = query_workspace(
            &[("a.nix", "let fooHelper = 1; myFoo = 2; in fooHelper")],
            "foo",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        let prefix_pos = names.iter().position(|n| *n == "fooHelper");
        let substr_pos = names.iter().position(|n| *n == "myFoo");
        assert!(
            prefix_pos.is_some() && substr_pos.is_some(),
            "both should be present, got: {names:?}"
        );
        assert!(
            prefix_pos < substr_pos,
            "prefix match should come before substring match, got: {names:?}"
        );
    }

    #[test]
    fn nested_attrset_children_are_flattened() {
        let results = query_workspace(
            &[("a.nix", "{ outer = { inner = 42; }; }")],
            "inner",
        );
        let names: Vec<&str> = results.iter().map(|s| s.name.as_str()).collect();
        assert!(
            names.contains(&"inner"),
            "nested child should be flattened into results, got: {names:?}"
        );
        // The container_name for "inner" should be "outer".
        let inner = results.iter().find(|s| s.name == "inner").unwrap();
        assert_eq!(
            inner.container_name.as_deref(),
            Some("outer"),
            "inner's container should be outer"
        );
    }

    #[test]
    fn symbol_kinds_preserved() {
        let results = query_workspace(
            &[("a.nix", "let f = x: x; y = 1; in f y")],
            "",
        );
        let func = results.iter().find(|s| s.name == "f").unwrap();
        assert_eq!(func.kind, SymbolKind::FUNCTION, "lambda binding should be FUNCTION");

        let var = results.iter().find(|s| s.name == "y").unwrap();
        assert_eq!(var.kind, SymbolKind::VARIABLE, "let binding should be VARIABLE");
    }

    #[test]
    fn no_match_returns_empty() {
        let results = query_workspace(
            &[("a.nix", "let x = 1; in x")],
            "zzzznotfound",
        );
        assert!(results.is_empty(), "non-matching query should return empty");
    }

    #[test]
    fn match_quality_fn_works_correctly() {
        assert_eq!(match_quality("foo", "foo"), Some(MatchQuality::Exact));
        assert_eq!(match_quality("foobar", "foo"), Some(MatchQuality::Prefix));
        assert_eq!(match_quality("barfoo", "foo"), Some(MatchQuality::Substring));
        assert_eq!(match_quality("bar", "foo"), None);
        assert_eq!(match_quality("anything", ""), Some(MatchQuality::Substring));
    }
}
