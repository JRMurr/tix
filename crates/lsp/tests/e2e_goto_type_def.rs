mod common;

use common::{LspTestHarness, TIMEOUT};
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Go-to-type-definition on a name with a Named alias type should jump to the
/// `.tix` file where the alias is declared.
#[tokio::test]
async fn goto_type_def_named_alias() {
    let mut h = LspTestHarness::new(&[
        (
            "tix.toml",
            indoc! {r#"
                stubs = ["types.tix"]
            "#},
        ),
        (
            "types.tix",
            indoc! {"
                type MyRecord = { name: string, count: int };
                val mkRecord :: string -> MyRecord;
            "},
        ),
        (
            "test.nix",
            indoc! {"
                let r = mkRecord \"foo\";
                in r
                #  ^1
            "},
        ),
    ])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let result = h
        .goto_type_def("test.nix", m[&1].line, m[&1].character)
        .await
        .expect("goto_type_def should return a result");

    let loc = match result {
        GotoDefinitionResponse::Scalar(loc) => loc,
        GotoDefinitionResponse::Array(locs) => locs.into_iter().next().unwrap(),
        GotoDefinitionResponse::Link(links) => {
            Location::new(links[0].target_uri.clone(), links[0].target_range)
        }
    };

    // The target URI should be the types.tix file.
    let types_uri = Url::from_file_path(h.workspace.path("types.tix")).unwrap();
    assert_eq!(
        loc.uri, types_uri,
        "goto_type_def should point to the .tix file"
    );

    // The range should cover the `type MyRecord = ...;` declaration.
    // Just verify it starts at line 0 (the type alias is on the first line).
    assert_eq!(
        loc.range.start.line, 0,
        "type alias should be on line 0 of types.tix"
    );

    h.shutdown().await;
}

/// Go-to-type-definition on a plain int should return None (no alias).
#[tokio::test]
async fn goto_type_def_plain_type_returns_null() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
            #              ^1
        "},
    )])
    .await;

    h.open("test.nix").await;
    let _ = h.wait_for_diagnostics("test.nix", TIMEOUT).await;

    let m = h.markers("test.nix");

    let result = h
        .goto_type_def("test.nix", m[&1].line, m[&1].character)
        .await;

    assert!(
        result.is_none(),
        "plain int should not have a type definition"
    );

    h.shutdown().await;
}
