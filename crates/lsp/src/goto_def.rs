// ==============================================================================
// textDocument/definition — jump to where a name is defined
// ==============================================================================
//
// For a Reference expression under the cursor, looks up name resolution to
// find the definition NameId, then maps that back to a source location via
// the source map.
//
// Cross-file support:
// - `import ./foo.nix` → jumps to the target file
// - `x.child` where `x = import ./foo.nix` → jumps to `child` in foo.nix

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstDb, AstPtr, Expr, Literal};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Location, Position, Range, Url};

use crate::state::{AnalysisState, FileAnalysis};

/// Try to find the definition location for the symbol at the given cursor position.
pub fn goto_definition(
    state: &AnalysisState,
    analysis: &FileAnalysis,
    pos: Position,
    uri: &Url,
    root: &rnix::Root,
) -> Option<Location> {
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    log::debug!(
        "goto_definition: pos={pos:?}, token={:?} {:?}",
        token.kind(),
        token.text()
    );

    // Walk up from the token to find a node that maps to an expression.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            log::debug!(
                "goto_definition: matched expr_id={expr_id:?}, expr={:?}",
                &analysis.module[expr_id]
            );

            // Cross-file: if this expression is part of `import <path>`, jump to the file.
            if let Some(target_path) = analysis.import_targets.get(&expr_id) {
                let target_uri = Url::from_file_path(target_path).ok()?;
                return Some(Location::new(
                    target_uri,
                    Range::new(Position::new(0, 0), Position::new(0, 0)),
                ));
            }

            // Cross-file: if this is a Select field name (Literal(String)), and the
            // Select's base expression is bound to an import, jump to the field's
            // definition in the target file.
            if let Expr::Literal(Literal::String(field_name)) = &analysis.module[expr_id] {
                if let Some(location) = try_resolve_select_field(state, analysis, &node, field_name)
                {
                    return Some(location);
                }
            }

            // Same-file: Reference expressions resolve via name resolution.
            if matches!(&analysis.module[expr_id], Expr::Reference(_)) {
                if let Some(res) = analysis.name_res.get(expr_id) {
                    match res {
                        ResolveResult::Definition(name_id) => {
                            // Find the source location of the definition.
                            if let Some(def_ptr) =
                                analysis.source_map.nodes_for_name(*name_id).next()
                            {
                                let def_node = def_ptr.to_node(root.syntax());
                                let range = analysis.line_index.range(def_node.text_range());
                                return Some(Location::new(uri.clone(), range));
                            }
                        }
                        // Builtins and `with` expressions don't have a source
                        // definition we can jump to within this file.
                        ResolveResult::Builtin(_) | ResolveResult::WithExprs(_) => {}
                    }
                }
            }
            // Found an expression node but can't resolve it — stop walking.
            return None;
        }

        node = node.parent()?;
    }
}

// ==============================================================================
// Select-through-imports: `x.child` where `x = import ./foo.nix`
// ==============================================================================

/// Given a field-name expression inside a Select, try to resolve it across files.
///
/// Walks up the syntax tree from `field_node` to find the enclosing Select,
/// resolves the Select's base to an import target, then finds the field
/// definition in the target file.
///
/// Limitations:
/// - Only handles single-level Select through a direct import binding.
///   `x.a.b` where `a` is a nested attrset won't cross-file resolve `b`.
/// - Alias chaining (`y = x; y.child` where `x = import ...`) doesn't follow.
///   Only direct `let x = import ...; x.child` works.
/// - Field name matching finds the first name with matching text in the target
///   module's top-level names. Nested scopes with the same name may cause
///   incorrect jumps.
fn try_resolve_select_field(
    state: &AnalysisState,
    analysis: &FileAnalysis,
    field_node: &rowan::SyntaxNode<rnix::NixLanguage>,
    field_name: &str,
) -> Option<Location> {
    log::debug!("try_resolve_select_field: field_name={field_name:?}");

    // Walk up from the field node to find the enclosing Select syntax node.
    let select_node = field_node.ancestors().find_map(rnix::ast::Select::cast)?;

    // Get the Select's base expression (`x` in `x.child`).
    let base_syntax = select_node.expr()?;
    let base_ptr = AstPtr::new(base_syntax.syntax());
    let base_expr_id = analysis.source_map.expr_for_node(base_ptr)?;

    log::debug!(
        "try_resolve_select_field: base_expr={:?}",
        &analysis.module[base_expr_id]
    );

    // Resolve the base to an import target path. Two cases:
    // 1. Base is directly an import Apply: check import_targets.
    // 2. Base is a Reference resolving to a name bound to an import: check name_to_import.
    let target_path = if let Some(path) = analysis.import_targets.get(&base_expr_id) {
        log::debug!(
            "try_resolve_select_field: direct import target -> {}",
            path.display()
        );
        path
    } else if let Expr::Reference(ref_name) = &analysis.module[base_expr_id] {
        let res = analysis.name_res.get(base_expr_id)?;
        log::debug!(
            "try_resolve_select_field: base is Reference({ref_name:?}), resolves to {res:?}"
        );
        if let ResolveResult::Definition(name_id) = res {
            let result = analysis.name_to_import.get(name_id);
            log::debug!(
                "try_resolve_select_field: name_to_import lookup for {:?} -> {:?}",
                analysis.module[*name_id].text,
                result
            );
            result?
        } else {
            return None;
        }
    } else {
        log::debug!("try_resolve_select_field: base is not a reference or import target");
        return None;
    };

    // Load the target file and find the field definition.
    let target_file = state.db.load_file(target_path)?;
    let (target_module, target_source_map) =
        lang_ast::module_and_source_maps(&state.db, target_file);
    let target_contents = target_file.contents(&state.db);
    let target_root = rnix::Root::parse(target_contents).tree();

    // Find a name in the target module matching the field name.
    let (target_name_id, _) = target_module
        .names()
        .find(|(_, name)| name.text == field_name)?;

    let target_ptr = target_source_map.nodes_for_name(target_name_id).next()?;
    let target_node = target_ptr.to_node(target_root.syntax());
    let target_line_index = crate::convert::LineIndex::new(target_contents);
    let target_range = target_line_index.range(target_node.text_range());
    let target_uri = Url::from_file_path(target_path).ok()?;
    Some(Location::new(target_uri, target_range))
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, temp_path};
    use lang_check::aliases::TypeAliasRegistry;
    use std::path::PathBuf;

    /// Create a temp directory with Nix files, returning the directory path.
    /// Files are written as `(relative_name, contents)` pairs.
    struct TempProject {
        dir: PathBuf,
    }

    impl TempProject {
        fn new(files: &[(&str, &str)]) -> Self {
            let dir = temp_path("project");
            std::fs::create_dir_all(&dir).expect("create temp dir");
            for (name, contents) in files {
                let path = dir.join(name);
                std::fs::write(&path, contents).expect("write temp file");
            }
            TempProject { dir }
        }

        fn path(&self, name: &str) -> PathBuf {
            self.dir.join(name).canonicalize().expect("canonicalize")
        }
    }

    impl Drop for TempProject {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    /// Build an AnalysisState and analyze a file, returning everything needed
    /// to call goto_definition.
    fn analyze(state: &mut AnalysisState, path: &PathBuf) -> (Url, String) {
        let contents = std::fs::read_to_string(path).expect("read file");
        state.update_file(path.clone(), contents.clone());
        let uri = Url::from_file_path(path).expect("path to uri");
        (uri, contents)
    }

    // ------------------------------------------------------------------
    // Same-file: let x = 1; in x  →  jumps to `x` definition
    // ------------------------------------------------------------------
    #[test]
    fn same_file_reference() {
        let project = TempProject::new(&[("ref.nix", "let x = 1; in x")]);
        let path = project.path("ref.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &path);
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        // Position the cursor on the trailing `x` (the reference).
        let ref_offset = find_offset(&contents, "in x") + 3; // the `x` after `in `
        let pos = analysis.line_index.position(ref_offset);

        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve same-file reference");

        // Should jump to the definition `x` in `let x = 1`.
        assert_eq!(loc.uri, uri);
        let def_offset = find_offset(&contents, "x = 1");
        let expected_pos = analysis.line_index.position(def_offset);
        assert_eq!(loc.range.start, expected_pos);
    }

    // ------------------------------------------------------------------
    // Import path: import ./lib.nix  →  jumps to lib.nix
    // ------------------------------------------------------------------
    #[test]
    fn import_path_jumps_to_file() {
        let project = TempProject::new(&[("main.nix", "import ./lib.nix"), ("lib.nix", "42")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `import` keyword.
        let pos = Position::new(0, 0);
        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve import to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri);
        assert_eq!(loc.range.start, Position::new(0, 0));
    }

    #[test]
    fn import_path_literal_jumps_to_file() {
        let project = TempProject::new(&[("main.nix", "import ./lib.nix"), ("lib.nix", "42")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on the path literal `./lib.nix`.
        let path_offset = find_offset(&contents, "./lib.nix");
        let pos = analysis.line_index.position(path_offset);
        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve path literal to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri);
    }

    // ------------------------------------------------------------------
    // Select through import: lib.x where lib = import ./lib.nix
    // ------------------------------------------------------------------
    #[test]
    fn select_through_import_jumps_to_field() {
        let project = TempProject::new(&[
            ("main.nix", "let lib = import ./lib.nix; in lib.x"),
            ("lib.nix", "{ x = 1; y = 2; }"),
        ]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `x` in `lib.x` (the field name after the dot).
        let select_offset = find_offset(&contents, "lib.x") + 4; // the `x` after dot
        let pos = analysis.line_index.position(select_offset);
        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve select field to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri, "should jump to lib.nix");

        // Verify the target position points to the `x` definition in lib.nix.
        let lib_contents = std::fs::read_to_string(&lib_path).unwrap();
        let lib_line_index = crate::convert::LineIndex::new(&lib_contents);
        let expected_offset = find_offset(&lib_contents, "x = 1");
        let expected_pos = lib_line_index.position(expected_offset);
        assert_eq!(loc.range.start, expected_pos);
    }

    // ------------------------------------------------------------------
    // Select through applied import: rustAttrs.rust-shell
    // where rustAttrs = import ./rust.nix { inherit pkgs; }
    // ------------------------------------------------------------------
    #[test]
    fn select_through_applied_import() {
        let project = TempProject::new(&[
            (
                "main.nix",
                "let attrs = import ./lib.nix { x = 1; }; in attrs.name",
            ),
            ("lib.nix", "{ x }: { name = x; value = 2; }"),
        ]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `name` in `attrs.name`.
        let select_offset = find_offset(&contents, "attrs.name") + 6; // the `n` in `name`
        let pos = analysis.line_index.position(select_offset);
        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve select field through applied import");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri, "should jump to lib.nix");

        // Verify the target position points to the `name` definition in lib.nix.
        let lib_contents = std::fs::read_to_string(&lib_path).unwrap();
        let lib_line_index = crate::convert::LineIndex::new(&lib_contents);
        let expected_offset = find_offset(&lib_contents, "name = x");
        let expected_pos = lib_line_index.position(expected_offset);
        assert_eq!(loc.range.start, expected_pos);
    }

    // ------------------------------------------------------------------
    // No result for non-navigable expressions
    // ------------------------------------------------------------------
    #[test]
    fn literal_returns_none() {
        let project = TempProject::new(&[("lit.nix", "42")]);
        let path = project.path("lit.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &path);
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(&contents).tree();

        let pos = Position::new(0, 0);
        let loc = goto_definition(&state, analysis, pos, &uri, &root);
        assert!(loc.is_none(), "literal should not resolve to a definition");
    }
}
