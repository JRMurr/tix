mod common;

use common::LspTestHarness;
use indoc::indoc;
use tower_lsp::lsp_types::*;

/// Go-to-definition on a let-binding reference resolves to the definition site.
#[tokio::test]
async fn goto_def_same_file() {
    let mut h = LspTestHarness::new(&[(
        "test.nix",
        indoc! {"
            let x = 42; in x
            #   ^1         ^2
        "},
    )])
    .await;

    h.open_and_wait("test.nix").await;

    let m = h.markers("test.nix");

    // Go-to-def on the reference `x` should jump to the definition.
    let result = h
        .goto_def("test.nix", m[&2].line, m[&2].character)
        .await
        .expect("goto_def should return a result");

    let target_pos = match result {
        GotoDefinitionResponse::Scalar(loc) => loc.range.start,
        GotoDefinitionResponse::Array(locs) => locs[0].range.start,
        GotoDefinitionResponse::Link(links) => links[0].target_range.start,
    };

    assert_eq!(
        target_pos, m[&1],
        "goto_def should point to the definition of x"
    );

    h.shutdown().await;
}

/// Go-to-definition across files: `a.x` in b.nix resolves into a.nix.
#[tokio::test]
async fn goto_def_cross_file() {
    let mut h = LspTestHarness::new(&[
        (
            "a.nix",
            indoc! {"
                { x = 42; }
                # ^1
            "},
        ),
        (
            "b.nix",
            indoc! {"
                let a = import ./a.nix;
                in a.x
                #    ^2
            "},
        ),
    ])
    .await;

    h.open_and_wait("a.nix").await;
    h.open_and_wait("b.nix").await;

    let m_b = h.markers("b.nix");

    let result = h
        .goto_def("b.nix", m_b[&2].line, m_b[&2].character)
        .await
        .expect("goto_def should return a cross-file result");

    // The target should be in a.nix, not b.nix.
    let target_uri = match &result {
        GotoDefinitionResponse::Scalar(loc) => &loc.uri,
        GotoDefinitionResponse::Array(locs) => &locs[0].uri,
        GotoDefinitionResponse::Link(links) => &links[0].target_uri,
    };

    let a_uri = Url::from_file_path(h.workspace.path("a.nix")).unwrap();
    assert_eq!(target_uri, &a_uri, "goto_def target should be in a.nix");

    h.shutdown().await;
}

/// Go-to-definition through a barrel re-export: `lib.val` where barrel.nix
/// has `{ val = import ./real.nix; }` should follow through to real.nix.
#[tokio::test]
async fn goto_def_through_barrel_reexport() {
    let mut h = LspTestHarness::new(&[
        ("real.nix", "42"),
        ("barrel.nix", "{ val = import ./real.nix; }"),
        (
            "main.nix",
            indoc! {"
                let lib = import ./barrel.nix;
                in lib.val
                #      ^1
            "},
        ),
    ])
    .await;

    h.open_and_wait("barrel.nix").await;
    h.open_and_wait("main.nix").await;

    let m = h.markers("main.nix");
    let result = h
        .goto_def("main.nix", m[&1].line, m[&1].character)
        .await
        .expect("goto_def should return a result");

    let target_uri = match &result {
        GotoDefinitionResponse::Scalar(loc) => &loc.uri,
        GotoDefinitionResponse::Array(locs) => &locs[0].uri,
        GotoDefinitionResponse::Link(links) => &links[0].target_uri,
    };

    let real_uri = Url::from_file_path(h.workspace.path("real.nix")).unwrap();
    assert_eq!(
        target_uri, &real_uri,
        "goto_def should follow through barrel to real.nix"
    );

    h.shutdown().await;
}

/// Go-to-definition through a pass-through barrel: barrel.nix imports
/// default.nix and returns it directly, so `res.hello` should land in default.nix.
#[tokio::test]
async fn goto_def_through_passthrough_barrel() {
    let mut h = LspTestHarness::new(&[
        (
            "default.nix",
            indoc! {"
                { hello = 42; }
                # ^1
            "},
        ),
        ("barrel.nix", "let res = import ./default.nix; in res"),
        (
            "main.nix",
            indoc! {"
                let res = import ./barrel.nix;
                in res.hello
                #      ^2
            "},
        ),
    ])
    .await;

    h.open_and_wait("default.nix").await;
    h.open_and_wait("barrel.nix").await;
    h.open_and_wait("main.nix").await;

    let m_main = h.markers("main.nix");
    let m_default = h.markers("default.nix");
    let result = h
        .goto_def("main.nix", m_main[&2].line, m_main[&2].character)
        .await
        .expect("goto_def should return a result");

    let (target_uri, target_pos) = match &result {
        GotoDefinitionResponse::Scalar(loc) => (&loc.uri, loc.range.start),
        GotoDefinitionResponse::Array(locs) => (&locs[0].uri, locs[0].range.start),
        GotoDefinitionResponse::Link(links) => (&links[0].target_uri, links[0].target_range.start),
    };

    let default_uri = Url::from_file_path(h.workspace.path("default.nix")).unwrap();
    assert_eq!(
        target_uri, &default_uri,
        "goto_def should follow through passthrough barrel to default.nix"
    );
    assert_eq!(
        target_pos, m_default[&1],
        "goto_def should point to hello definition in default.nix"
    );

    h.shutdown().await;
}

/// When the barrel binding is NOT an import, goto-def should stop at the
/// barrel file's binding (existing behavior preserved).
#[tokio::test]
async fn goto_def_barrel_non_import_stops() {
    let mut h = LspTestHarness::new(&[
        (
            "barrel.nix",
            indoc! {"
                { val = 42; }
                # ^1
            "},
        ),
        (
            "main.nix",
            indoc! {"
                let lib = import ./barrel.nix;
                in lib.val
                #      ^2
            "},
        ),
    ])
    .await;

    h.open_and_wait("barrel.nix").await;
    h.open_and_wait("main.nix").await;

    let m_main = h.markers("main.nix");
    let m_barrel = h.markers("barrel.nix");
    let result = h
        .goto_def("main.nix", m_main[&2].line, m_main[&2].character)
        .await
        .expect("goto_def should return a result");

    let (target_uri, target_pos) = match &result {
        GotoDefinitionResponse::Scalar(loc) => (&loc.uri, loc.range.start),
        GotoDefinitionResponse::Array(locs) => (&locs[0].uri, locs[0].range.start),
        GotoDefinitionResponse::Link(links) => (&links[0].target_uri, links[0].target_range.start),
    };

    let barrel_uri = Url::from_file_path(h.workspace.path("barrel.nix")).unwrap();
    assert_eq!(
        target_uri, &barrel_uri,
        "goto_def should land in barrel.nix for non-import binding"
    );
    assert_eq!(
        target_pos, m_barrel[&1],
        "goto_def should point to val definition in barrel.nix"
    );

    h.shutdown().await;
}
