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

    // Walk up from the token to find a node that maps to an expression.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
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
                if let Some(location) =
                    try_resolve_select_field(state, analysis, &node, field_name)
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
    // Walk up from the field node to find the enclosing Select syntax node.
    let select_node = field_node
        .ancestors()
        .find_map(rnix::ast::Select::cast)?;

    // Get the Select's base expression (`x` in `x.child`).
    let base_syntax = select_node.expr()?;
    let base_ptr = AstPtr::new(base_syntax.syntax());
    let base_expr_id = analysis.source_map.expr_for_node(base_ptr)?;

    // Resolve the base to an import target path. Two cases:
    // 1. Base is directly an import Apply: check import_targets.
    // 2. Base is a Reference resolving to a name bound to an import: check name_to_import.
    let target_path = if let Some(path) = analysis.import_targets.get(&base_expr_id) {
        path
    } else if let Expr::Reference(_) = &analysis.module[base_expr_id] {
        let res = analysis.name_res.get(base_expr_id)?;
        if let ResolveResult::Definition(name_id) = res {
            analysis.name_to_import.get(name_id)?
        } else {
            return None;
        }
    } else {
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
