mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Let-bindings produce a nested DocumentSymbol tree.
#[tokio::test]
async fn symbols_let_bindings() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let
              alpha = 1;
              beta = \"hello\";
            in alpha + beta
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let result = h
        .document_symbols("test.nix")
        .await
        .expect("document_symbols should return a result");

    let symbols = match result {
        DocumentSymbolResponse::Flat(syms) => {
            // Flat response — just check we have symbols.
            assert!(!syms.is_empty(), "should have symbols");
            return h.shutdown().await;
        }
        DocumentSymbolResponse::Nested(syms) => syms,
    };

    // Collect all symbol names (including children).
    fn collect_names(syms: &[DocumentSymbol]) -> Vec<String> {
        let mut names = Vec::new();
        for s in syms {
            names.push(s.name.clone());
            if let Some(children) = &s.children {
                names.extend(collect_names(children));
            }
        }
        names
    }

    let names = collect_names(&symbols);
    assert!(
        names.iter().any(|n| n == "alpha"),
        "should contain symbol 'alpha', got: {names:?}"
    );
    assert!(
        names.iter().any(|n| n == "beta"),
        "should contain symbol 'beta', got: {names:?}"
    );

    h.shutdown().await;
}

/// Nested attrset fields appear as children in the symbol tree.
#[tokio::test]
async fn symbols_nested_attrset() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            {
              outer = {
                inner = 42;
              };
            }
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let result = h
        .document_symbols("test.nix")
        .await
        .expect("document_symbols should return a result");

    match result {
        DocumentSymbolResponse::Flat(syms) => {
            assert!(!syms.is_empty(), "should have symbols");
        }
        DocumentSymbolResponse::Nested(syms) => {
            // Look for "outer" with a child "inner".
            fn find_symbol<'a>(
                syms: &'a [DocumentSymbol],
                name: &str,
            ) -> Option<&'a DocumentSymbol> {
                for s in syms {
                    if s.name == name {
                        return Some(s);
                    }
                    if let Some(children) = &s.children {
                        if let Some(found) = find_symbol(children, name) {
                            return Some(found);
                        }
                    }
                }
                None
            }

            let outer = find_symbol(&syms, "outer").expect("should have an 'outer' symbol");
            let children = outer
                .children
                .as_ref()
                .expect("'outer' should have children");
            assert!(
                children.iter().any(|c| c.name == "inner"),
                "outer should have 'inner' child, got: {:?}",
                children.iter().map(|c| &c.name).collect::<Vec<_>>()
            );
        }
    }

    h.shutdown().await;
}
