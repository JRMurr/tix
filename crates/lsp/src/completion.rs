// ==============================================================================
// textDocument/completion — auto-complete attrset fields
// ==============================================================================
//
// Two completion contexts:
//
// 1. **Dot completion** — cursor after `.` in a Select expression (e.g. `lib.`).
//    Resolves the base expression's type, walks through any already-typed path
//    segments, then offers the remaining fields.
//
// 2. **Callsite attrset completion** — cursor inside `{ }` that is a function
//    argument (e.g. `mkDerivation { | }`). Looks up the function's parameter
//    type and suggests fields not already present.

use std::collections::BTreeMap;

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr, ExprId, NameKind};
use lang_ty::{OutputTy, TyRef};
use rowan::ast::AstNode;
use smol_str::SmolStr;
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionResponse, Position,
};

use crate::state::FileAnalysis;

/// Entry point: try to produce completions for the given cursor position.
pub fn completion(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
) -> Option<CompletionResponse> {
    let inference = analysis.inference()?;
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        // left_biased: when cursor is right after `.`, we want the `.` token itself
        // (not the whitespace/ident to the right).
        .left_biased()?;

    log::debug!(
        "completion: pos={pos:?}, token={:?} {:?}",
        token.kind(),
        token.text()
    );

    // Try dot completion first (cursor right after `.` in a Select).
    if let Some(items) = try_dot_completion(analysis, inference, &token) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Try callsite attrset completion (cursor inside `{ }` argument).
    if let Some(items) = try_callsite_completion(analysis, inference, &token) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    None
}

// ==============================================================================
// Dot completion: `lib.` or `lib.strings.`
// ==============================================================================

fn try_dot_completion(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    // Walk ancestors from the token's parent to find a Select node.
    let node = token.parent()?;
    let select_node = node
        .ancestors()
        .find_map(rnix::ast::Select::cast)?;

    // Get the base expression of the Select (e.g. `lib` in `lib.strings.x`).
    let base_expr = select_node.expr()?;
    let base_ptr = AstPtr::new(base_expr.syntax());
    let base_expr_id = analysis.source_map.expr_for_node(base_ptr)?;

    // Collect the already-typed path segments (everything before the cursor).
    // For `lib.strings.`, the attrpath has segments ["strings", <missing>].
    // We resolve through each complete segment to get the nested type.
    //
    // We pass the cursor offset so that segments injected by rnix's error
    // recovery AFTER the cursor position are excluded.
    let cursor_offset = token.text_range().end();
    let typed_segments = collect_typed_segments(&select_node, cursor_offset);

    // Resolve the base expression's type. Try the direct expr_ty_map first;
    // if that yields a bare type variable (common for lambda parameters),
    // fall back to extracting the type from the enclosing lambda.
    let base_ty = resolve_base_type(analysis, inference, base_expr_id)?;

    log::debug!(
        "dot_completion: base_ty={base_ty}, typed_segments={typed_segments:?}"
    );

    // Walk through the typed segments to resolve the nested type.
    // If segment resolution fails (e.g. the type doesn't have the expected
    // field, or error-recovery injected a bogus segment), fall back to just
    // showing the base type's fields.
    let resolved_ty = resolve_through_segments(&base_ty, &typed_segments)
        .unwrap_or(base_ty);

    // Extract fields from the resolved type and build completion items.
    let fields = collect_attrset_fields(&resolved_ty);
    Some(fields_to_completion_items(&fields))
}

/// Resolve the type of a base expression for dot completion.
///
/// Tries expr_ty_map first. If that yields a bare type variable (common for
/// lambda parameters whose concrete type only exists at call sites), falls
/// back to:
/// 1. name_ty_map via name resolution (helps for let-bindings with richer names).
/// 2. Extracting the param type from the enclosing Lambda's canonicalized type.
///    The Lambda type captures constraints from within the body AND from call
///    sites when the function and its call are in the same analysis unit.
fn resolve_base_type(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    base_expr_id: ExprId,
) -> Option<OutputTy> {
    // Primary: direct expr_ty_map lookup.
    if let Some(ty) = inference.expr_ty_map.get(&base_expr_id) {
        if !collect_attrset_fields(ty).is_empty() {
            return Some(ty.clone());
        }
    }

    // Fallback: resolve through name resolution.
    let resolve_result = analysis.name_res.get(base_expr_id)?;
    let name_id = match resolve_result {
        ResolveResult::Definition(name_id) => *name_id,
        _ => {
            // For `with` expressions, try the expr_ty_map type even if it
            // has no attrset fields (it may still be useful after segment resolution).
            return inference.expr_ty_map.get(&base_expr_id).cloned();
        }
    };

    // Check name_ty_map for a concrete type.
    if let Some(name_ty) = inference.name_ty_map.get(&name_id) {
        if !collect_attrset_fields(name_ty).is_empty() {
            return Some(name_ty.clone());
        }
    }

    // For lambda parameters, extract the param type from the enclosing
    // Lambda's canonicalized type.
    let name = &analysis.module[name_id];
    if matches!(name.kind, NameKind::Param | NameKind::PatField) {
        if let Some(lambda_expr_id) = find_lambda_for_param(&analysis.module, name_id) {
            if let Some(lambda_ty) = inference.expr_ty_map.get(&lambda_expr_id) {
                log::debug!(
                    "dot_completion fallback: lambda ty={lambda_ty} for param {:?}",
                    name.text
                );
                if let Some(param_ty) = extract_lambda_param(lambda_ty) {
                    // For PatField names (e.g. `pkgs` in `{ pkgs, ... }: body`),
                    // the lambda param type is the whole pattern attrset
                    // `{ pkgs: T, ... }`. We need the specific field's type `T`,
                    // not the entire attrset.
                    if name.kind == NameKind::PatField {
                        let fields = collect_attrset_fields(&param_ty);
                        if let Some(field_ty) = fields.get(&name.text) {
                            return Some((*field_ty.0).clone());
                        }
                    }
                    return Some(param_ty);
                }
            }
        }
    }

    // Last resort: return whatever expr_ty_map has, even if it's a TyVar.
    inference.expr_ty_map.get(&base_expr_id).cloned()
}

/// Find the Lambda ExprId that owns the given parameter NameId.
fn find_lambda_for_param(module: &lang_ast::Module, param_name: lang_ast::NameId) -> Option<ExprId> {
    for (expr_id, expr) in module.exprs() {
        if let Expr::Lambda { param, pat, .. } = expr {
            // Direct parameter: `pkgs: body`
            if *param == Some(param_name) {
                return Some(expr_id);
            }
            // Pattern field: `{ pkgs, ... }: body`
            if let Some(pat) = pat {
                if pat.fields.iter().any(|(n, _)| *n == Some(param_name)) {
                    return Some(expr_id);
                }
            }
        }
    }
    None
}

/// Collect the attrpath segments that have already been typed (i.e. that have
/// a string literal in the lowered AST). The final segment (the one being
/// completed) is excluded because it maps to `Expr::Missing` or doesn't exist.
///
/// `cursor_offset` filters out segments that rnix's error recovery may have
/// injected from tokens after the cursor position.
fn collect_typed_segments(
    select: &rnix::ast::Select,
    cursor_offset: rowan::TextSize,
) -> Vec<SmolStr> {
    let mut segments = Vec::new();

    let Some(attrpath) = select.attrpath() else {
        return segments;
    };

    for attr in attrpath.attrs() {
        // Skip attrs that start at or after the cursor — they're either the
        // segment being completed or artifacts from error recovery.
        if attr.syntax().text_range().start() >= cursor_offset {
            break;
        }

        // Try to extract the static name from this Attr.
        let name = match attr {
            rnix::ast::Attr::Ident(ref ident) => {
                ident.ident_token().map(|t| SmolStr::from(t.text()))
            }
            rnix::ast::Attr::Str(ref s) => {
                // Try to get a simple string literal.
                get_str_literal(s)
            }
            rnix::ast::Attr::Dynamic(_) => None,
        };

        match name {
            Some(n) if !n.is_empty() => segments.push(n),
            _ => break,
        }
    }

    segments
}

/// Extract a plain string literal from an rnix Str node (no interpolation).
fn get_str_literal(s: &rnix::ast::Str) -> Option<SmolStr> {
    // normalized_parts() returns InterpolPart<String> with escape sequences resolved.
    let parts = s.normalized_parts();
    if parts.len() != 1 {
        return None;
    }
    match &parts[0] {
        rnix::ast::InterpolPart::Literal(lit) => Some(SmolStr::from(lit.as_str())),
        rnix::ast::InterpolPart::Interpolation(_) => None,
    }
}

/// Walk a type through a series of field names, resolving each one.
fn resolve_through_segments(ty: &OutputTy, segments: &[SmolStr]) -> Option<OutputTy> {
    let mut current = ty.clone();
    for seg in segments {
        let fields = collect_attrset_fields(&current);
        let field_ty = fields.get(seg)?;
        current = (*field_ty.0).clone();
    }
    Some(current)
}

// ==============================================================================
// Callsite attrset completion: `f { | }`
// ==============================================================================

fn try_callsite_completion(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    let node = token.parent()?;

    // Find the enclosing AttrSet syntax node.
    let attrset_node = node
        .ancestors()
        .find_map(rnix::ast::AttrSet::cast)?;

    // Check if the AttrSet's parent is an Apply node (i.e. it's a function argument).
    let apply_node = attrset_node
        .syntax()
        .parent()
        .and_then(rnix::ast::Apply::cast)?;

    // Get the function expression from the Apply.
    let fun_expr = apply_node.lambda()?;
    let fun_ptr = AstPtr::new(fun_expr.syntax());
    let fun_expr_id = analysis.source_map.expr_for_node(fun_ptr)?;

    // Look up the function's type.
    let fun_ty = inference.expr_ty_map.get(&fun_expr_id)?;

    log::debug!("callsite_completion: fun_ty={fun_ty}");

    // Extract the parameter type from the function type.
    let param_ty = extract_lambda_param(fun_ty)?;

    // Get expected fields from the parameter type.
    let expected_fields = collect_attrset_fields(&param_ty);
    if expected_fields.is_empty() {
        return None;
    }

    // Collect fields already present in the attrset literal to filter them out.
    let existing = collect_existing_fields(analysis, &attrset_node);

    log::debug!(
        "callsite_completion: expected={:?}, existing={existing:?}",
        expected_fields.keys().collect::<Vec<_>>()
    );

    // Return only the fields that haven't been written yet.
    let remaining: BTreeMap<SmolStr, TyRef> = expected_fields
        .into_iter()
        .filter(|(k, _)| !existing.contains(k))
        .collect();

    Some(fields_to_completion_items(&remaining))
}

/// Collect field names already present in an attrset literal, using the lowered
/// AST (Bindings) rather than re-parsing rnix. We look up the AttrSet's ExprId
/// in the source map and read its static binding names from the Module.
fn collect_existing_fields(
    analysis: &FileAnalysis,
    attrset_node: &rnix::ast::AttrSet,
) -> Vec<SmolStr> {
    let ptr = AstPtr::new(attrset_node.syntax());
    let Some(expr_id) = analysis.source_map.expr_for_node(ptr) else {
        return Vec::new();
    };

    match &analysis.module[expr_id] {
        Expr::AttrSet { bindings, .. } => bindings
            .statics
            .iter()
            .map(|(name_id, _)| analysis.module[*name_id].text.clone())
            .collect(),
        _ => Vec::new(),
    }
}

// ==============================================================================
// Type unwrapping helpers
// ==============================================================================

/// Extract attrset fields from a type, unwrapping Named, Intersection, and Union
/// wrappers as appropriate.
fn collect_attrset_fields(ty: &OutputTy) -> BTreeMap<SmolStr, TyRef> {
    match ty {
        OutputTy::AttrSet(attr) => attr.fields.clone(),

        // Named wraps an alias around an inner type — look through it.
        OutputTy::Named(_, inner) => collect_attrset_fields(&inner.0),

        // Intersection of attrsets: merge all fields (a field present in any
        // member is available).
        OutputTy::Intersection(members) => {
            let mut merged = BTreeMap::new();
            for m in members {
                for (k, v) in collect_attrset_fields(&m.0) {
                    merged.entry(k).or_insert(v);
                }
            }
            merged
        }

        // Union of attrsets: only fields present in ALL members are safe to
        // complete on.
        OutputTy::Union(members) => {
            let mut iter = members.iter();
            let Some(first) = iter.next() else {
                return BTreeMap::new();
            };
            let mut common = collect_attrset_fields(&first.0);
            for m in iter {
                let member_fields = collect_attrset_fields(&m.0);
                common.retain(|k, _| member_fields.contains_key(k));
            }
            common
        }

        _ => BTreeMap::new(),
    }
}

/// Extract the parameter type from a function type.
fn extract_lambda_param(ty: &OutputTy) -> Option<OutputTy> {
    match ty {
        OutputTy::Lambda { param, .. } => Some((*param.0).clone()),
        OutputTy::Named(_, inner) => extract_lambda_param(&inner.0),
        // For an intersection of lambdas (overloaded function), try the first
        // member that's a lambda.
        OutputTy::Intersection(members) => {
            for m in members {
                if let Some(param) = extract_lambda_param(&m.0) {
                    return Some(param);
                }
            }
            None
        }
        _ => None,
    }
}

// ==============================================================================
// CompletionItem construction
// ==============================================================================

fn fields_to_completion_items(fields: &BTreeMap<SmolStr, TyRef>) -> Vec<CompletionItem> {
    fields
        .iter()
        .map(|(name, ty)| CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::FIELD),
            detail: Some(format!("{ty}")),
            ..Default::default()
        })
        .collect()
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use lang_check::aliases::TypeAliasRegistry;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU32, Ordering};

    static COUNTER: AtomicU32 = AtomicU32::new(0);

    fn temp_path(name: &str) -> PathBuf {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!(
            "tix_completion_test_{}_{id}_{name}",
            std::process::id()
        ))
    }

    /// Analyze source and get completions at a given byte offset.
    fn complete_at(src: &str, offset: u32) -> Vec<CompletionItem> {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();
        let pos = analysis.line_index.position(offset);

        match completion(analysis, pos, &root) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        }
    }

    /// Find the byte offset of a pattern in source, with an additional offset.
    fn find_offset(src: &str, pattern: &str, extra: usize) -> u32 {
        (src.find(pattern).expect("pattern not found") + extra) as u32
    }

    fn labels(items: &[CompletionItem]) -> Vec<&str> {
        items.iter().map(|i| i.label.as_str()).collect()
    }

    // ------------------------------------------------------------------
    // Dot completion
    // ------------------------------------------------------------------

    #[test]
    fn dot_completion_simple() {
        // Place cursor right after the dot in `lib.`
        let src = "let lib = { x = 1; y = \"hello\"; }; in lib.";
        let offset = find_offset(src, "lib.", 4); // right after the dot
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(names.contains(&"x"), "should complete x, got: {names:?}");
        assert!(names.contains(&"y"), "should complete y, got: {names:?}");
    }

    #[test]
    fn dot_completion_nested() {
        let src = "let lib = { strings = { concat = 1; sep = 2; }; }; in lib.strings.";
        let offset = find_offset(src, "lib.strings.", 12);
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(
            names.contains(&"concat"),
            "should complete concat, got: {names:?}"
        );
        assert!(
            names.contains(&"sep"),
            "should complete sep, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // Callsite completion
    // ------------------------------------------------------------------

    #[test]
    fn callsite_completion_basic() {
        let src = "let f = { name, src, ... }: name; in f { }";
        // Cursor inside the `{ }` — right after `{` and space.
        let offset = find_offset(src, "f { }", 3);
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(
            names.contains(&"name"),
            "should complete name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "should complete src, got: {names:?}"
        );
    }

    #[test]
    fn dot_completion_inside_list() {
        let src = "let pkgs = { hello = 1; gcc = 2; }; in [ pkgs. ]";
        let offset = find_offset(src, "pkgs.", 5); // right after the dot
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(
            names.contains(&"hello"),
            "should complete hello inside list, got: {names:?}"
        );
        assert!(
            names.contains(&"gcc"),
            "should complete gcc inside list, got: {names:?}"
        );
    }

    #[test]
    fn dot_completion_lambda_param() {
        // When a function is called BEFORE the incomplete expression, the call
        // site parses cleanly and its argument type constrains the lambda parameter.
        // The lambda param fallback extracts the param type from the Lambda's
        // canonicalized type.
        let src = "let f = pkgs: pkgs; r = f { hello = 1; gcc = 2; }; in r.";
        let offset = find_offset(src, "r.", 2);
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(
            names.contains(&"hello"),
            "should complete hello from called lambda, got: {names:?}"
        );
        assert!(
            names.contains(&"gcc"),
            "should complete gcc from called lambda, got: {names:?}"
        );
    }

    #[test]
    fn dot_completion_lambda_param_body() {
        // Inside a lambda body, the parameter's type comes from the Lambda's
        // own canonicalized type. When the lambda body already uses known
        // fields from the parameter, those fields appear in completions.
        let src = "let f = pkgs: pkgs.name + pkgs.; in f { name = \"x\"; src = ./.; }";
        let offset = find_offset(src, "pkgs.;", 5);
        let items = complete_at(src, offset);
        let names = labels(&items);
        // The lambda param type captures within-body constraints: at minimum
        // "name" (from `pkgs.name`). "src" comes from the call site which
        // may or may not survive rnix error recovery.
        eprintln!("lambda_param_body completions: {names:?}");
        assert!(
            names.contains(&"name"),
            "should complete name from within-body constraint, got: {names:?}"
        );
    }

    #[test]
    fn dot_completion_pat_param() {
        // Pattern parameter: `{ pkgs, ... }: body`. The patfield's type is
        // extracted from the Lambda param type's matching field.
        // When the patfield is used with known selectors, those appear.
        let src = "let f = { pkgs, ... }: pkgs.name + pkgs.; in f { pkgs = { name = \"x\"; src = ./.; }; }";
        let offset = find_offset(src, "pkgs.;", 5);
        let items = complete_at(src, offset);
        let names = labels(&items);
        eprintln!("pat_param completions: {names:?}");
        assert!(
            names.contains(&"name"),
            "should complete name from within-body usage, got: {names:?}"
        );
    }

    #[test]
    fn callsite_completion_filters_existing() {
        let src = "let f = { name, src, ... }: name; in f { name = \"x\"; }";
        // Cursor after `name = "x"; ` inside the braces.
        let offset = find_offset(src, "\"x\"; }", 5);
        let items = complete_at(src, offset);
        let names = labels(&items);
        assert!(
            !names.contains(&"name"),
            "should NOT complete already-present name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "should complete src, got: {names:?}"
        );
    }

}
