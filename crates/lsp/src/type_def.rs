// ==============================================================================
// textDocument/typeDefinition — jump to alias definition in .tix stubs
// ==============================================================================
//
// For a name or expression with a `Named` alias type, looks up the alias
// definition location in the TypeAliasRegistry and returns an LSP Location
// pointing to the `.tix` stub file where the alias is declared.

use lang_ast::{AstPtr, Expr, Literal};
use lang_check::aliases::TypeAliasRegistry;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::state::FileSnapshot;
use crate::ty_nav::extract_alias_name;

/// Try to find the type definition locations for the symbol at the given cursor position.
///
/// Returns LSP `Location`s pointing to the `.tix` file(s) where the alias is
/// declared. Multiple locations when an alias is defined across several stub
/// files (e.g. `module pkgs` in both `lib.tix` and `generated/pkgs.tix`).
/// Returns an empty vec if the type is not a named alias or the alias has no
/// recorded source location (e.g. compiled-in stubs).
pub fn goto_type_definition(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
    registry: &TypeAliasRegistry,
) -> Vec<Location> {
    let Some(inference) = analysis.inference_result() else {
        return Vec::new();
    };
    let offset = analysis.syntax.line_index.offset(pos);
    let Some(token) = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()
    else {
        return Vec::new();
    };

    // Walk up from the token to find a node that maps to a name or expression.
    let Some(mut node) = token.parent() else {
        return Vec::new();
    };
    loop {
        let ptr = AstPtr::new(&node);

        // Check for a name binding first.
        if let Some(name_id) = analysis.syntax.source_map.name_for_node(ptr) {
            if let Some(&ty_ref) = inference.name_ty_map.get(name_id) {
                return resolve_decl_locations(
                    extract_alias_name(&inference.arena[ty_ref]),
                    registry,
                );
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            if let Some(&ty_ref) = inference.expr_ty_map.get(expr_id) {
                let locs =
                    resolve_decl_locations(extract_alias_name(&inference.arena[ty_ref]), registry);
                if !locs.is_empty() {
                    return locs;
                }
            }
            // Fallback: if this is a select field name with no Named alias,
            // try looking up the field name as a stub val declaration.
            if let Expr::Literal(Literal::String(field_name)) = &analysis.syntax.module[expr_id] {
                let locs = resolve_decl_locations(Some(field_name), registry);
                if !locs.is_empty() {
                    return locs;
                }
            }
            return Vec::new();
        }

        let Some(parent) = node.parent() else {
            return Vec::new();
        };
        node = parent;
    }
}

/// Given an optional alias name, look up all source locations and convert each
/// to an LSP Location. Reads each `.tix` file from disk to build a LineIndex
/// for byte-to-position conversion.
///
/// For module declarations the recorded span covers the entire block
/// (`module pkgs { ... }`). We trim it to just the header line (up to and
/// including the `{`) so VSCode doesn't try to highlight a huge range.
fn resolve_decl_locations(
    alias_name: Option<&smol_str::SmolStr>,
    registry: &TypeAliasRegistry,
) -> Vec<Location> {
    let Some(name) = alias_name else {
        return Vec::new();
    };
    registry
        .decl_locations(name)
        .iter()
        .filter_map(|loc| {
            let source = std::fs::read_to_string(&loc.file_path).ok()?;
            let span_end = trim_to_header(&source, loc.span);
            let line_index = crate::convert::LineIndex::new(&source);
            let start = line_index.position(loc.span.0 as u32);
            let end = line_index.position(span_end as u32);
            let uri = Url::from_file_path(&loc.file_path).ok()?;
            Some(Location::new(
                uri,
                tower_lsp::lsp_types::Range::new(start, end),
            ))
        })
        .collect()
}

/// If the span text contains a `{`, return the byte offset just past it
/// (the header of a module declaration). Otherwise return the original end.
fn trim_to_header(source: &str, span: (usize, usize)) -> usize {
    let text = &source[span.0..span.1];
    match text.find('{') {
        Some(offset) => span.0 + offset + 1,
        None => span.1,
    }
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{parse_markers, TestAnalysis};
    use indoc::indoc;
    use lang_check::aliases::TypeAliasRegistry;
    use std::path::PathBuf;

    /// Helper: create a registry with a stub file on disk, returning the
    /// registry and the stub file path.
    fn registry_with_stub(stub_content: &str) -> (TypeAliasRegistry, PathBuf) {
        let stub_path = crate::test_util::temp_path("test.tix");
        std::fs::write(&stub_path, stub_content).expect("write stub");
        let mut registry = TypeAliasRegistry::default();
        let file = comment_parser::parse_tix_file(stub_content).expect("parse stub");
        registry.load_tix_file_with_path(&file, &stub_path);
        (registry, stub_path)
    }

    #[test]
    fn type_def_named_alias() {
        let stub = "type Derivation = { name: string, system: string };";
        let (registry, stub_path) = registry_with_stub(stub);

        let src = indoc! {"
            let
                /** type: drv :: Derivation */
                drv = { name = \"hello\"; system = \"x86_64-linux\"; };
            in drv
            #  ^1
        "};
        let markers = parse_markers(src);

        let ta = TestAnalysis::with_registry(src, registry.clone());
        let snap = ta.snapshot();
        let root = ta.root;

        let pos = snap.syntax.line_index.position(markers[&1]);
        let locs = goto_type_definition(&snap, pos, &root, &registry);
        assert_eq!(
            locs.len(),
            1,
            "should resolve to exactly one alias definition"
        );
        let loc = &locs[0];

        // Should point to the stub file.
        let expected_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(loc.uri, expected_uri);

        // Clean up.
        let _ = std::fs::remove_file(&stub_path);
    }

    #[test]
    fn type_def_plain_type_returns_none() {
        let src = indoc! {"
            let x = 42; in x
            #              ^1
        "};
        let markers = parse_markers(src);

        let registry = TypeAliasRegistry::default();
        let ta = TestAnalysis::with_registry(src, registry.clone());
        let snap = ta.snapshot();
        let root = ta.root;

        let pos = snap.syntax.line_index.position(markers[&1]);
        let locs = goto_type_definition(&snap, pos, &root, &registry);
        assert!(
            locs.is_empty(),
            "plain int should not resolve to a type definition"
        );
    }

    #[test]
    fn type_def_module_alias() {
        let stub = indoc! {"
            module lib {
                val id :: a -> a;
            }
        "};
        let (registry, stub_path) = registry_with_stub(stub);

        let src = indoc! {"
            let
                /** type: lib :: Lib */
                lib = { id = x: x; };
            in lib
            #  ^1
        "};
        let markers = parse_markers(src);

        let ta = TestAnalysis::with_registry(src, registry.clone());
        let snap = ta.snapshot();
        let root = ta.root;

        let pos = snap.syntax.line_index.position(markers[&1]);
        let locs = goto_type_definition(&snap, pos, &root, &registry);
        assert_eq!(
            locs.len(),
            1,
            "should resolve module alias to one definition"
        );
        let loc = &locs[0];

        let expected_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(loc.uri, expected_uri);

        let _ = std::fs::remove_file(&stub_path);
    }

    #[test]
    fn type_def_field_name_fallback_to_val_decl() {
        // When a field's type is not Named (e.g. a lambda), go-to-type-definition
        // should fall back to the stub val declaration for the field name.
        let stub = indoc! {"
            module pkgs {
                val fetchurl :: { url: string } -> string;
            }
        "};
        let (registry, stub_path) = registry_with_stub(stub);

        let src = indoc! {"
            let
                /** type: pkgs :: Pkgs */
                pkgs = { fetchurl = url: url; };
            in pkgs.fetchurl
            #       ^1
        "};
        let markers = parse_markers(src);

        let ta = TestAnalysis::with_registry(src, registry.clone());
        let snap = ta.snapshot();
        let root = ta.root;

        let pos = snap.syntax.line_index.position(markers[&1]);
        let locs = goto_type_definition(&snap, pos, &root, &registry);
        assert_eq!(
            locs.len(),
            1,
            "should resolve field name to stub val declaration"
        );
        let loc = &locs[0];
        let expected_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(loc.uri, expected_uri);

        let _ = std::fs::remove_file(&stub_path);
    }

    #[test]
    fn type_def_builtin_stubs_have_no_location() {
        // with_builtins() loads compiled-in stubs — no file path.
        let registry = TypeAliasRegistry::with_builtins();
        // "Lib" is defined in the builtin stubs.
        assert!(
            registry.decl_locations("Lib").is_empty(),
            "compiled-in stubs should not have locations"
        );
    }

    #[test]
    fn type_def_multiple_stubs_return_multiple_locations() {
        let stub_a = "module pkgs { val hello :: string; }";
        let stub_b = "module pkgs { val gcc :: string; }";

        let path_a = crate::test_util::temp_path("a.tix");
        let path_b = crate::test_util::temp_path("b.tix");
        std::fs::write(&path_a, stub_a).expect("write stub a");
        std::fs::write(&path_b, stub_b).expect("write stub b");

        let mut registry = TypeAliasRegistry::default();
        let file_a = comment_parser::parse_tix_file(stub_a).expect("parse a");
        let file_b = comment_parser::parse_tix_file(stub_b).expect("parse b");
        registry.load_tix_file_with_path(&file_a, &path_a);
        registry.load_tix_file_with_path(&file_b, &path_b);

        let src = indoc! {"
            let
                /** type: pkgs :: Pkgs */
                pkgs = { hello = \"hi\"; gcc = \"gcc\"; };
            in pkgs
            #  ^1
        "};
        let markers = parse_markers(src);

        let ta = TestAnalysis::with_registry(src, registry.clone());
        let snap = ta.snapshot();
        let root = ta.root;

        let pos = snap.syntax.line_index.position(markers[&1]);
        let locs = goto_type_definition(&snap, pos, &root, &registry);
        assert_eq!(
            locs.len(),
            2,
            "should return locations from both stub files"
        );

        let uri_a = Url::from_file_path(&path_a).unwrap();
        let uri_b = Url::from_file_path(&path_b).unwrap();
        assert_eq!(locs[0].uri, uri_a);
        assert_eq!(locs[1].uri, uri_b);

        let _ = std::fs::remove_file(&path_a);
        let _ = std::fs::remove_file(&path_b);
    }
}
