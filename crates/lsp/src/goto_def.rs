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
// - Unresolved names that match a `val` in .tix stubs → jumps to the stub
// - `lib.field` where `field` matches a stub val → jumps to the stub

use std::collections::HashMap;
use std::path::PathBuf;

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstDb, AstPtr, Expr, Literal};
use lang_check::aliases::DeclLocation;
use rowan::ast::AstNode;
use smol_str::SmolStr;
use tower_lsp::lsp_types::{Location, Position, Range, Url};

use crate::state::{AnalysisState, FileSnapshot};

/// Try to find the definition location for the symbol at the given cursor position.
pub fn goto_definition(
    state: &AnalysisState,
    analysis: &FileSnapshot,
    pos: Position,
    uri: &Url,
    root: &rnix::Root,
) -> Option<Location> {
    let offset = analysis.syntax.line_index.offset(pos);
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

        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            log::debug!(
                "goto_definition: matched expr_id={expr_id:?}, expr={:?}",
                &analysis.syntax.module[expr_id]
            );

            // Cross-file: if this expression is part of `import <path>`, jump to the file.
            if let Some(target_path) = analysis.syntax.import_targets.get(&expr_id) {
                let target_uri = Url::from_file_path(target_path).ok()?;
                return Some(Location::new(
                    target_uri,
                    Range::new(Position::new(0, 0), Position::new(0, 0)),
                ));
            }

            // Cross-file: if this is a Select field name (Literal(String)), and the
            // Select's base expression is bound to an import, jump to the field's
            // definition in the target file. Falls back to stub val declarations
            // for fields like `lib.someFunction` where `lib` comes from a stub module.
            if let Expr::Literal(Literal::String(field_name)) = &analysis.syntax.module[expr_id] {
                if let Some(location) = try_resolve_select_field(state, analysis, &node, field_name)
                {
                    return Some(location);
                }
                if let Some(location) = decl_location_to_lsp(
                    state.registry.decl_locations(field_name).first(),
                    state.registry.source_roots(),
                ) {
                    return Some(location);
                }
            }

            // Any path literal not already handled by import_targets: resolve
            // the path on disk (including directory→default.nix) and jump to it.
            // This makes bare path literals like `./lib.nix` or `./pkg` clickable
            // regardless of whether they appear in an import, callPackage, or other context.
            if let Expr::Literal(Literal::Path(path_str)) = &analysis.syntax.module[expr_id] {
                let base_dir = uri.to_file_path().ok()?.parent()?.to_path_buf();
                if let Some(resolved) = crate::state::resolve_nix_path(&base_dir, path_str) {
                    let target_uri = Url::from_file_path(&resolved).ok()?;
                    return Some(Location::new(
                        target_uri,
                        Range::new(Position::new(0, 0), Position::new(0, 0)),
                    ));
                }
            }

            // Same-file: Reference expressions resolve via name resolution.
            // When name resolution has no result (unresolved name), fall back
            // to stub val declarations — e.g. `mkDerivation` provided by a
            // .tix stub file.
            if let Expr::Reference(ref_name) = &analysis.syntax.module[expr_id] {
                if let Some(res) = analysis.syntax.name_res.get(expr_id) {
                    match res {
                        ResolveResult::Definition(name_id) => {
                            // Find the source location of the definition.
                            if let Some(def_ptr) =
                                analysis.syntax.source_map.nodes_for_name(*name_id).next()
                            {
                                let def_node = def_ptr.to_node(root.syntax());
                                let range = analysis.syntax.line_index.range(def_node.text_range());
                                return Some(Location::new(uri.clone(), range));
                            }
                        }
                        // Builtins and `with` expressions don't have a source
                        // definition we can jump to within this file.
                        ResolveResult::Builtin(_) | ResolveResult::WithExprs(..) => {}
                    }
                } else if let Some(location) = decl_location_to_lsp(
                    state.registry.decl_locations(ref_name.as_str()).first(),
                    state.registry.source_roots(),
                ) {
                    return Some(location);
                }
            }
            // Found an expression node but can't resolve it — stop walking.
            return None;
        }

        node = node.parent()?;
    }
}

// ==============================================================================
// Stub declaration → LSP Location conversion
// ==============================================================================

/// Convert a `DeclLocation` from the registry into an LSP `Location`.
///
/// When the declaration has an `@source` annotation and the corresponding source
/// root is configured, returns a location in the original source (e.g. nixpkgs)
/// instead of the `.tix` stub file. Falls back to the stub location if the source
/// can't be resolved.
pub(crate) fn decl_location_to_lsp(
    loc: Option<&DeclLocation>,
    source_roots: &HashMap<SmolStr, PathBuf>,
) -> Option<Location> {
    let loc = loc?;

    // Prefer the original source location when available and resolvable.
    if let Some(ref src) = loc.source {
        if let Some(resolved) = resolve_source_location(src, source_roots) {
            return Some(resolved);
        }
    }

    // Fall back to the .tix stub file location.
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

/// Resolve a `SourceLocation` (from `@source` annotation) to an LSP `Location`
/// by looking up the source root and constructing an absolute path.
fn resolve_source_location(
    src: &comment_parser::SourceLocation,
    source_roots: &HashMap<SmolStr, PathBuf>,
) -> Option<Location> {
    // Split path on first `:` to get (source_id, relative_path).
    let colon_idx = src.path.find(':')?;
    let source_id = &src.path[..colon_idx];
    let relative_path = &src.path[colon_idx + 1..];

    let root = source_roots.get(source_id)?;
    let abs_path = root.join(relative_path);
    if !abs_path.exists() {
        return None;
    }

    let uri = Url::from_file_path(&abs_path).ok()?;
    // Nix positions are 1-based; LSP positions are 0-based.
    let pos = Position::new(src.line.saturating_sub(1), src.column.saturating_sub(1));
    Some(Location::new(uri, Range::new(pos, pos)))
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
    analysis: &FileSnapshot,
    field_node: &rowan::SyntaxNode<rnix::NixLanguage>,
    field_name: &str,
) -> Option<Location> {
    log::debug!("try_resolve_select_field: field_name={field_name:?}");

    // Walk up from the field node to find the enclosing Select syntax node.
    let select_node = field_node.ancestors().find_map(rnix::ast::Select::cast)?;

    // Get the Select's base expression (`x` in `x.child`).
    let base_syntax = select_node.expr()?;
    let base_ptr = AstPtr::new(base_syntax.syntax());
    let base_expr_id = analysis.syntax.source_map.expr_for_node(base_ptr)?;

    log::debug!(
        "try_resolve_select_field: base_expr={:?}",
        &analysis.syntax.module[base_expr_id]
    );

    // Resolve the base to an import target path. Two cases:
    // 1. Base is directly an import Apply: check import_targets.
    // 2. Base is a Reference resolving to a name bound to an import: check name_to_import.
    let target_path = if let Some(path) = analysis.syntax.import_targets.get(&base_expr_id) {
        log::debug!(
            "try_resolve_select_field: direct import target -> {}",
            path.display()
        );
        path
    } else if let Expr::Reference(ref_name) = &analysis.syntax.module[base_expr_id] {
        let res = analysis.syntax.name_res.get(base_expr_id)?;
        log::debug!(
            "try_resolve_select_field: base is Reference({ref_name:?}), resolves to {res:?}"
        );
        if let ResolveResult::Definition(name_id) = res {
            let result = analysis.syntax.name_to_import.get(name_id);
            log::debug!(
                "try_resolve_select_field: name_to_import lookup for {:?} -> {:?}",
                analysis.syntax.module[*name_id].text,
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

    // If the target path is a directory, Nix loads `default.nix` from it.
    let resolved_target = if target_path.is_dir() {
        target_path.join("default.nix")
    } else {
        target_path.clone()
    };

    // Load the target file and find the field definition.
    let target_file = state.db.load_file(&resolved_target)?;
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
    let target_uri = Url::from_file_path(&resolved_target).ok()?;
    Some(Location::new(target_uri, target_range))
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, parse_markers, TempProject};
    use indoc::indoc;
    use lang_check::aliases::TypeAliasRegistry;
    use std::path::PathBuf;

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
        let src = indoc! {"
            let x = 1; in x
            #   ^1        ^2
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("ref.nix", src)]);
        let path = project.path("ref.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &path);
        let analysis = state.get_file(&path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on the trailing `x` (the reference).
        let pos = analysis.syntax.line_index.position(markers[&2]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve same-file reference");

        // Should jump to the definition `x` in `let x = 1`.
        assert_eq!(loc.uri, uri);
        let expected_pos = analysis.syntax.line_index.position(markers[&1]);
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
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `import` keyword.
        let pos = Position::new(0, 0);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve import to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri);
        assert_eq!(loc.range.start, Position::new(0, 0));
    }

    #[test]
    fn import_path_literal_jumps_to_file() {
        let src = indoc! {"
            import ./lib.nix
            #      ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src), ("lib.nix", "42")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on the path literal `./lib.nix`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve path literal to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri);
    }

    // ------------------------------------------------------------------
    // Select through import: lib.x where lib = import ./lib.nix
    // ------------------------------------------------------------------
    #[test]
    fn select_through_import_jumps_to_field() {
        let src = indoc! {"
            let lib = import ./lib.nix; in lib.x
            #                                  ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src), ("lib.nix", "{ x = 1; y = 2; }")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `x` in `lib.x` (the field name after the dot).
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
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
        let src = indoc! {"
            let attrs = import ./lib.nix { x = 1; }; in attrs.name
            #                                                 ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[
            ("main.nix", src),
            ("lib.nix", "{ x }: { name = x; value = 2; }"),
        ]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `name` in `attrs.name`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
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
    // Select through path-literal heuristic: x.field where
    // x = pkgs.callPackage ./pkg.nix { }
    // ------------------------------------------------------------------
    #[test]
    fn select_through_callpackage_path_literal() {
        let src = indoc! {"
            let x = someFn ./pkg.nix { a = 1; }; in x.name
            #                                          ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[
            ("main.nix", src),
            ("pkg.nix", "{ a }: { name = a; value = 2; }"),
        ]);
        let main_path = project.path("main.nix");
        let pkg_path = project.path("pkg.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `name` in `x.name`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve select field via path literal heuristic");

        let pkg_uri = Url::from_file_path(&pkg_path).unwrap();
        assert_eq!(loc.uri, pkg_uri, "should jump to pkg.nix");

        let pkg_contents = std::fs::read_to_string(&pkg_path).unwrap();
        let pkg_line_index = crate::convert::LineIndex::new(&pkg_contents);
        let expected_offset = find_offset(&pkg_contents, "name = a");
        let expected_pos = pkg_line_index.position(expected_offset);
        assert_eq!(loc.range.start, expected_pos);
    }

    // ------------------------------------------------------------------
    // Select through path-literal with directory → default.nix
    // ------------------------------------------------------------------
    #[test]
    fn select_through_callpackage_directory() {
        let src = indoc! {"
            let x = someFn ./pkg { a = 1; }; in x.name
            #                                      ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[
            ("main.nix", src),
            ("pkg/default.nix", "{ a }: { name = a; value = 2; }"),
        ]);
        let main_path = project.path("main.nix");
        let pkg_path = project.path("pkg/default.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `name` in `x.name`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve select field via directory path literal");

        let pkg_uri = Url::from_file_path(&pkg_path).unwrap();
        assert_eq!(loc.uri, pkg_uri, "should jump to pkg/default.nix");

        let pkg_contents = std::fs::read_to_string(&pkg_path).unwrap();
        let pkg_line_index = crate::convert::LineIndex::new(&pkg_contents);
        let expected_offset = find_offset(&pkg_contents, "name = a");
        let expected_pos = pkg_line_index.position(expected_offset);
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
        let analysis = state.get_file(&path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let pos = Position::new(0, 0);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        assert!(loc.is_none(), "literal should not resolve to a definition");
    }

    // ------------------------------------------------------------------
    // Bare path literal: ./lib.nix  →  jumps to lib.nix
    // ------------------------------------------------------------------
    #[test]
    fn bare_path_literal_jumps_to_file() {
        let src = indoc! {"
            let x = ./lib.nix; in x
            #       ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src), ("lib.nix", "42")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on the path literal `./lib.nix`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("bare path literal should resolve to target file");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        assert_eq!(loc.uri, lib_uri);
        assert_eq!(loc.range.start, Position::new(0, 0));
    }

    // ------------------------------------------------------------------
    // Directory path literal: ./pkg  →  jumps to pkg/default.nix
    // ------------------------------------------------------------------
    #[test]
    fn bare_path_literal_directory_jumps_to_default_nix() {
        let src = indoc! {"
            let x = ./pkg; in x
            #       ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src), ("pkg/default.nix", "{ name = 1; }")]);
        let main_path = project.path("main.nix");
        let pkg_default = project.path("pkg/default.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on the path literal `./pkg`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("directory path literal should resolve to default.nix");

        let pkg_uri = Url::from_file_path(&pkg_default).unwrap();
        assert_eq!(loc.uri, pkg_uri, "should jump to pkg/default.nix");
        assert_eq!(loc.range.start, Position::new(0, 0));
    }

    // ------------------------------------------------------------------
    // Helper: create a registry with a stub file on disk
    // ------------------------------------------------------------------
    fn registry_with_stub(stub_content: &str) -> (TypeAliasRegistry, PathBuf) {
        let stub_path = crate::test_util::temp_path("test.tix");
        std::fs::write(&stub_path, stub_content).expect("write stub");
        let mut registry = TypeAliasRegistry::default();
        let file = comment_parser::parse_tix_file(stub_content).expect("parse stub");
        registry.load_tix_file_with_path(&file, &stub_path);
        (registry, stub_path)
    }

    // ------------------------------------------------------------------
    // Unresolved reference → stub val declaration
    // ------------------------------------------------------------------
    #[test]
    fn unresolved_ref_jumps_to_stub_val() {
        let stub = "val mkDerivation :: { name: string } -> int;";
        let (registry, stub_path) = registry_with_stub(stub);

        let src = indoc! {"
            mkDerivation { name = \"hello\"; }
            # ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src)]);
        let main_path = project.path("main.nix");

        let mut state = AnalysisState::new(registry);
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `mkDerivation` — an unresolved name backed by a stub val.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve unresolved ref to stub val");

        let stub_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(loc.uri, stub_uri, "should jump to stub file");

        let _ = std::fs::remove_file(&stub_path);
    }

    // ------------------------------------------------------------------
    // Select field → stub val declaration (e.g. lib.id)
    // ------------------------------------------------------------------
    #[test]
    fn select_field_jumps_to_stub_val() {
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
            in lib.id 42
            #      ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src)]);
        let main_path = project.path("main.nix");

        let mut state = AnalysisState::new(registry);
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        // Cursor on `id` in `lib.id`.
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        let loc = loc.expect("should resolve select field to stub val");

        let stub_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(loc.uri, stub_uri, "should jump to stub file");

        let _ = std::fs::remove_file(&stub_path);
    }

    // ------------------------------------------------------------------
    // Unresolved ref with no stub → still returns None
    // ------------------------------------------------------------------
    #[test]
    fn unresolved_ref_no_stub_returns_none() {
        let src = indoc! {"
            unknownFunction 42
            # ^1
        "};
        let markers = parse_markers(src);

        let project = TempProject::new(&[("main.nix", src)]);
        let main_path = project.path("main.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root);
        assert!(
            loc.is_none(),
            "unresolved ref with no stub should return None"
        );
    }

    // ------------------------------------------------------------------
    // @source annotation → jumps to original nixpkgs source
    // ------------------------------------------------------------------
    #[test]
    fn unresolved_ref_jumps_to_source_location() {
        let stub = indoc! {"
            @source nixpkgs:lib/trivial.nix:61:8
            val myFunc :: a -> a;
        "};

        let src = indoc! {"
            myFunc 42
            # ^1
        "};
        let markers = parse_markers(src);

        // Create a fake nixpkgs directory with a trivial.nix file.
        let nixpkgs_tmp = tempfile::tempdir().unwrap();
        let nixpkgs_dir = nixpkgs_tmp.path().to_path_buf();
        let lib_dir = nixpkgs_dir.join("lib");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("trivial.nix"), "{ myFunc = x: x; }").unwrap();

        let (mut registry, _stub_path) = registry_with_stub(stub);
        registry.set_source_root("nixpkgs", nixpkgs_dir.clone());

        let project = TempProject::new(&[("main.nix", src)]);
        let main_path = project.path("main.nix");

        let mut state = AnalysisState::new(registry);
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root)
            .expect("should resolve to nixpkgs source");

        // Should jump to the nixpkgs file, not the stub file.
        let expected_path = lib_dir.join("trivial.nix");
        let expected_uri = Url::from_file_path(&expected_path).unwrap();
        assert_eq!(loc.uri, expected_uri, "should jump to nixpkgs source");
        // Nix positions are 1-based, LSP is 0-based.
        assert_eq!(loc.range.start, Position::new(60, 7));
    }

    #[test]
    fn source_location_falls_back_to_stub_when_file_missing() {
        let stub = indoc! {"
            @source nixpkgs:lib/nonexistent.nix:10:3
            val myFunc :: a -> a;
        "};

        let src = indoc! {"
            myFunc 42
            # ^1
        "};
        let markers = parse_markers(src);

        let (mut registry, stub_path) = registry_with_stub(stub);
        // Set a source root but the file doesn't exist.
        registry.set_source_root("nixpkgs", PathBuf::from("/nonexistent/path"));

        let project = TempProject::new(&[("main.nix", src)]);
        let main_path = project.path("main.nix");

        let mut state = AnalysisState::new(registry);
        let (uri, contents) = analyze(&mut state, &main_path);
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let pos = analysis.syntax.line_index.position(markers[&1]);
        let loc = goto_definition(&state, &analysis, pos, &uri, &root)
            .expect("should fall back to stub location");

        // Should fall back to the stub file.
        let stub_uri = Url::from_file_path(&stub_path).unwrap();
        assert_eq!(
            loc.uri, stub_uri,
            "should fall back to stub when source missing"
        );

        let _ = std::fs::remove_file(&stub_path);
    }
}
