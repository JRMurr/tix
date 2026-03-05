// ==============================================================================
// textDocument/typeDefinition — jump to alias definition in .tix stubs
// ==============================================================================
//
// For a name or expression with a `Named` alias type, looks up the alias
// definition location in the TypeAliasRegistry and returns an LSP Location
// pointing to the `.tix` stub file where the alias is declared.

use lang_ast::AstPtr;
use lang_check::aliases::TypeAliasRegistry;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::state::FileSnapshot;
use crate::ty_nav::extract_alias_name;

/// Try to find the type definition location for the symbol at the given cursor position.
///
/// Returns an LSP `Location` pointing to the `.tix` file where the alias is
/// declared, or `None` if the type at the cursor is not a named alias or the
/// alias has no recorded source location (e.g. compiled-in stubs).
pub fn goto_type_definition(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
    registry: &TypeAliasRegistry,
) -> Option<Location> {
    let inference = analysis.inference_result()?;
    let offset = analysis.syntax.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    // Walk up from the token to find a node that maps to a name or expression.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Check for a name binding first.
        if let Some(name_id) = analysis.syntax.source_map.name_for_node(ptr) {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                return resolve_alias_location(extract_alias_name(ty), registry);
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            if let Some(ty) = inference.expr_ty_map.get(expr_id) {
                return resolve_alias_location(extract_alias_name(ty), registry);
            }
            // Found an expression node but no alias — stop walking.
            return None;
        }

        node = node.parent()?;
    }
}

/// Given an optional alias name, look up its source location and convert to
/// an LSP Location. Reads the `.tix` file from disk to build a LineIndex for
/// byte-to-position conversion.
fn resolve_alias_location(
    alias_name: Option<&smol_str::SmolStr>,
    registry: &TypeAliasRegistry,
) -> Option<Location> {
    let name = alias_name?;
    let loc = registry.alias_location(name)?;

    let source = std::fs::read_to_string(&loc.file_path).ok()?;
    let line_index = crate::convert::LineIndex::new(&source);
    let start = line_index.position(loc.span.0 as u32);
    let end = line_index.position(loc.span.1 as u32);

    let uri = Url::from_file_path(&loc.file_path).ok()?;
    Some(Location::new(
        uri,
        tower_lsp::lsp_types::Range::new(start, end),
    ))
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
        let loc = goto_type_definition(&snap, pos, &root, &registry);
        let loc = loc.expect("should resolve to alias definition");

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
        let loc = goto_type_definition(&snap, pos, &root, &registry);
        assert!(
            loc.is_none(),
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
        let loc = goto_type_definition(&snap, pos, &root, &registry);
        let loc = loc.expect("should resolve module alias to definition");

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
            registry.alias_location("Lib").is_none(),
            "compiled-in stubs should not have locations"
        );
    }
}
