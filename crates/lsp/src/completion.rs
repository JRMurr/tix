// ==============================================================================
// textDocument/completion
// ==============================================================================
//
// Completion strategies, tried in priority order:
//
// 1. **Dot completion** — cursor after `.` in a Select expression (e.g. `lib.`).
//    Resolves the base expression's type, walks through any already-typed path
//    segments, then offers the remaining fields.
//
// 2. **Callsite attrset completion** — cursor inside `{ }` that is a function
//    argument (e.g. `mkDerivation { | }`). Looks up the function's parameter
//    type and suggests fields not already present.
//
// 3. **Inherit completion** — cursor inside `inherit ...;`. For plain `inherit`,
//    suggests names from the enclosing scope. For `inherit (expr)`, suggests
//    fields from the expression's type.
//
// 4. **Identifier completion** — catch-all for any expression position. Suggests
//    all visible names (let bindings, lambda params, `with` env fields, builtins).

use std::collections::BTreeMap;

use lang_ast::nameres::{self, ResolveResult};
use lang_ast::{AstPtr, Expr, ExprId, NameKind};
use lang_ty::{OutputTy, TyRef};
use rowan::ast::AstNode;
use smol_str::SmolStr;
use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind, CompletionResponse, Position};

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

    // Try inherit completion (cursor inside `inherit ...;`).
    if let Some(items) = try_inherit_completion(analysis, inference, &token) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Catch-all: suggest all visible identifiers at the cursor position.
    if let Some(items) = try_identifier_completion(analysis, inference, &token) {
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
    let select_node = node.ancestors().find_map(rnix::ast::Select::cast)?;

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

    log::debug!("dot_completion: base_ty={base_ty}, typed_segments={typed_segments:?}");

    // Walk through the typed segments to resolve the nested type.
    // If segment resolution fails (e.g. the type doesn't have the expected
    // field, or error-recovery injected a bogus segment), fall back to just
    // showing the base type's fields.
    let resolved_ty = resolve_through_segments(&base_ty, &typed_segments).unwrap_or(base_ty);

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
fn find_lambda_for_param(
    module: &lang_ast::Module,
    param_name: lang_ast::NameId,
) -> Option<ExprId> {
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
    let attrset_node = node.ancestors().find_map(rnix::ast::AttrSet::cast)?;

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
// Inherit completion: `inherit ▊;` and `inherit (expr) ▊;`
// ==============================================================================

fn try_inherit_completion(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    let node = token.parent()?;

    // Walk ancestors to find an enclosing Inherit node.
    let inherit_node = node.ancestors().find_map(rnix::ast::Inherit::cast)?;

    // Collect names already present in this inherit clause so we can filter
    // them out. rnix models each inherited attr as an Ident inside the Inherit.
    let existing: Vec<SmolStr> = inherit_node
        .attrs()
        .filter_map(|attr| match attr {
            rnix::ast::Attr::Ident(ident) => ident.ident_token().map(|t| SmolStr::from(t.text())),
            _ => None,
        })
        .collect();

    if let Some(from) = inherit_node.from() {
        // `inherit (expr) ▊;` — suggest fields from the expression's type.
        let expr_node = from.expr()?;
        let expr_ptr = AstPtr::new(expr_node.syntax());
        let expr_id = analysis.source_map.expr_for_node(expr_ptr)?;
        let ty = inference.expr_ty_map.get(&expr_id)?;
        let fields = collect_attrset_fields(ty);

        let items = fields
            .iter()
            .filter(|(name, _)| !existing.contains(name))
            .map(|(name, ty)| CompletionItem {
                label: name.to_string(),
                kind: Some(CompletionItemKind::FIELD),
                detail: Some(format!("{ty}")),
                ..Default::default()
            })
            .collect();

        Some(items)
    } else {
        // `inherit ▊;` — suggest names from the enclosing scope.
        //
        // Find the enclosing LetIn or AttrSet syntax node, map it to an
        // ExprId, and get the scope registered for that expression. In
        // nameres.rs, scope_by_expr records the PARENT scope for LetIn/AttrSet
        // (before bindings are introduced), which is exactly the scope that
        // `inherit` pulls names from.
        let enclosing_expr_id = inherit_node.syntax().ancestors().find_map(|n| {
            // Try LetIn first, then AttrSet.
            if rnix::ast::LetIn::can_cast(n.kind()) || rnix::ast::AttrSet::can_cast(n.kind()) {
                let ptr = AstPtr::new(&n);
                analysis.source_map.expr_for_node(ptr)
            } else {
                None
            }
        })?;

        let scope_id = analysis.scopes.scope_for_expr(enclosing_expr_id)?;
        let visible = collect_visible_names(analysis, inference, scope_id);

        let items = visible
            .iter()
            .filter(|(name, _)| !existing.contains(name))
            .map(|(name, ty)| CompletionItem {
                label: name.to_string(),
                kind: Some(completion_kind_for_ty(ty.as_ref())),
                detail: ty.as_ref().map(|t| format!("{t}")),
                ..Default::default()
            })
            .collect();

        Some(items)
    }
}

// ==============================================================================
// Identifier completion: catch-all for expression positions
// ==============================================================================

fn try_identifier_completion(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    let scope_id = scope_at_token(analysis, token)?;
    let visible = collect_visible_names(analysis, inference, scope_id);

    let items: Vec<CompletionItem> = visible
        .iter()
        .map(|(name, ty)| CompletionItem {
            label: name.to_string(),
            kind: Some(completion_kind_for_ty(ty.as_ref())),
            detail: ty.as_ref().map(|t| format!("{t}")),
            ..Default::default()
        })
        .collect();

    Some(items)
}

// ==============================================================================
// Scope-walking helpers
// ==============================================================================

/// Find the scope at the given token by walking ancestor syntax nodes until one
/// maps to an ExprId with a registered scope.
///
/// When the token is whitespace (e.g. space between `in` and the body
/// expression), the parent node may be a container like LetIn whose registered
/// scope is the OUTER scope. In that case we try the next non-trivia token,
/// which is typically inside the inner expression with the correct scope.
fn scope_at_token(
    analysis: &FileAnalysis,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<nameres::ScopeId> {
    let effective_token = if matches!(
        token.kind(),
        rnix::SyntaxKind::TOKEN_WHITESPACE | rnix::SyntaxKind::TOKEN_COMMENT
    ) {
        token.next_token().unwrap_or_else(|| token.clone())
    } else {
        token.clone()
    };

    let node = effective_token.parent()?;
    for ancestor in node.ancestors() {
        let ptr = AstPtr::new(&ancestor);
        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            if let Some(scope_id) = analysis.scopes.scope_for_expr(expr_id) {
                return Some(scope_id);
            }
        }
    }
    None
}

/// Collect all names visible at a given scope, walking the scope chain from
/// inner to outer. Inner definitions shadow outer ones (first insertion wins).
///
/// For `WithExpr` scopes, extracts attrset fields from the env expression's
/// inferred type.
///
/// Appends global builtins at lowest priority.
fn collect_visible_names(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    scope_id: nameres::ScopeId,
) -> BTreeMap<SmolStr, Option<OutputTy>> {
    let mut result: BTreeMap<SmolStr, Option<OutputTy>> = BTreeMap::new();

    for scope_data in analysis.scopes.ancestors(scope_id) {
        if let Some(defs) = scope_data.as_definitions() {
            for (name, name_id) in defs {
                result
                    .entry(name.clone())
                    .or_insert_with(|| inference.name_ty_map.get(name_id).cloned());
            }
        } else if let Some(with_expr_id) = scope_data.as_with() {
            // The With expression's env is the first child.
            if let Expr::With { env, .. } = &analysis.module[with_expr_id] {
                if let Some(env_ty) = inference.expr_ty_map.get(env) {
                    for (field_name, field_ty) in collect_attrset_fields(env_ty) {
                        result
                            .entry(field_name)
                            .or_insert_with(|| Some((*field_ty.0).clone()));
                    }
                }
            }
        }
    }

    // Append builtins at lowest priority. We use `builtins` itself as a name
    // (it's a Nix global), plus all global builtins from nameres.
    let builtin_names = [
        "abort",
        "baseNameOf",
        "builtins",
        "derivation",
        "dirOf",
        "fetchGit",
        "fetchMercurial",
        "fetchTarball",
        "fetchTree",
        "fetchurl",
        "fromTOML",
        "import",
        "isNull",
        "map",
        "placeholder",
        "removeAttrs",
        "scopedImport",
        "throw",
        "toString",
        "true",
        "false",
        "null",
    ];
    for name in builtin_names {
        result.entry(SmolStr::from(name)).or_insert(None);
    }

    result
}

/// Map a type to the appropriate LSP CompletionItemKind.
fn completion_kind_for_ty(ty: Option<&OutputTy>) -> CompletionItemKind {
    match ty {
        Some(t) => {
            if is_function_ty(t) {
                CompletionItemKind::FUNCTION
            } else {
                CompletionItemKind::VARIABLE
            }
        }
        None => CompletionItemKind::VARIABLE,
    }
}

/// Check if a type is a function (Lambda), unwrapping Named wrappers.
fn is_function_ty(ty: &OutputTy) -> bool {
    match ty {
        OutputTy::Lambda { .. } => true,
        OutputTy::Named(_, inner) => is_function_ty(&inner.0),
        _ => false,
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
    use crate::test_util::{find_offset, temp_path};
    use lang_check::aliases::TypeAliasRegistry;

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

    fn labels(items: &[CompletionItem]) -> Vec<&str> {
        items.iter().map(|i| i.label.as_str()).collect()
    }

    // ==================================================================
    // Marker-based test infrastructure
    // ==================================================================
    //
    // Embed `# ^<num>` comments in the test source where `^` points to
    // the column on the PREVIOUS line where completion should trigger,
    // and `<num>` is a marker ID.
    //
    // Since `#` is a valid Nix comment, the markers don't affect parsing.

    /// Parse `# ^<num>` marker comments from source.
    /// Returns a BTreeMap from marker number to byte offset on the previous line.
    fn parse_markers(src: &str) -> BTreeMap<u32, u32> {
        let mut markers = BTreeMap::new();
        let lines: Vec<&str> = src.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            // Find all `^<num>` patterns in comment lines.
            let trimmed = line.trim();
            if !trimmed.starts_with('#') {
                continue;
            }

            let mut search_from = 0;
            while let Some(caret_pos) = line[search_from..].find('^') {
                let abs_caret_pos = search_from + caret_pos;
                let after_caret = &line[abs_caret_pos + 1..];

                // Parse the marker number immediately after `^`.
                let num_str: String = after_caret
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect();
                if num_str.is_empty() {
                    search_from = abs_caret_pos + 1;
                    continue;
                }
                let marker_num: u32 = num_str.parse().unwrap();

                // The column of `^` on the marker line corresponds to the
                // same column on the PREVIOUS line.
                assert!(line_idx > 0, "marker on first line has no previous line");
                let prev_line_start: usize = lines[..line_idx - 1]
                    .iter()
                    .map(|l| l.len() + 1) // +1 for the newline
                    .sum();

                let byte_offset = (prev_line_start + abs_caret_pos) as u32;
                markers.insert(marker_num, byte_offset);
                search_from = abs_caret_pos + 1 + num_str.len();
            }
        }

        markers
    }

    /// Run completions at all marker positions. Returns marker → completions.
    fn complete_at_markers(src: &str) -> BTreeMap<u32, Vec<CompletionItem>> {
        let markers = parse_markers(src);
        assert!(!markers.is_empty(), "no markers found in source");

        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = analysis.line_index.position(offset);
                let items = match completion(analysis, pos, &root) {
                    Some(CompletionResponse::Array(items)) => items,
                    _ => Vec::new(),
                };
                (num, items)
            })
            .collect()
    }

    // ------------------------------------------------------------------
    // Dot completion
    // ------------------------------------------------------------------

    #[test]
    fn dot_completion_simple() {
        let src = r#"
let lib = { x = 1; y = "hello"; };
in lib.
#      ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(names.contains(&"x"), "should complete x, got: {names:?}");
        assert!(names.contains(&"y"), "should complete y, got: {names:?}");
    }

    #[test]
    fn dot_completion_nested() {
        let src = r#"
let lib = { strings = { concat = 1; sep = 2; }; };
in lib.strings.
#              ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
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
        let src = r#"
let f = { name, src, ... }: name;
in f { }
#     ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
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
        let src = r#"
let pkgs = { hello = 1; gcc = 2; };
in [ pkgs. ]
#         ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
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
        let src = r#"
let f = pkgs: pkgs;
    r = f { hello = 1; gcc = 2; };
in r.
#    ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
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
        let src = r#"let f = pkgs: pkgs.name + pkgs.; in f { name = "x"; src = ./.; }"#;
        let offset = find_offset(src, "pkgs.;") + 5;
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
        let src = r#"let f = { pkgs, ... }: pkgs.name + pkgs.; in f { pkgs = { name = "x"; src = ./.; }; }"#;
        let offset = find_offset(src, "pkgs.;") + 5;
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
        let src = r#"
let f = { name, src, ... }: name;
in f { name = "x"; }
#                  ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            !names.contains(&"name"),
            "should NOT complete already-present name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "should complete src, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // Identifier completion
    // ------------------------------------------------------------------

    #[test]
    fn identifier_in_let_body() {
        let src = r#"
let x = 1; y = "hello";
in x
#  ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(names.contains(&"x"), "should suggest x, got: {names:?}");
        assert!(names.contains(&"y"), "should suggest y, got: {names:?}");
    }

    #[test]
    fn identifier_in_list() {
        let src = r#"
let pkgs = 1;
in [ pkgs ]
#    ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"pkgs"),
            "should suggest pkgs, got: {names:?}"
        );
    }

    #[test]
    fn identifier_includes_builtins() {
        let src = r#"
let x = 1;
in x
#  ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"import"),
            "should suggest import, got: {names:?}"
        );
        assert!(names.contains(&"map"), "should suggest map, got: {names:?}");
        assert!(
            names.contains(&"true"),
            "should suggest true, got: {names:?}"
        );
        assert!(
            names.contains(&"null"),
            "should suggest null, got: {names:?}"
        );
    }

    #[test]
    fn identifier_function_kind() {
        let src = r#"
let f = x: x;
in f
#  ^1
"#;
        let results = complete_at_markers(src);
        let f_item = results[&1]
            .iter()
            .find(|i| i.label == "f")
            .expect("should have f");
        assert_eq!(
            f_item.kind,
            Some(CompletionItemKind::FUNCTION),
            "lambda-typed name should get FUNCTION kind"
        );
    }

    // ------------------------------------------------------------------
    // With-scope completion
    // ------------------------------------------------------------------

    #[test]
    fn with_scope_completion() {
        let src = r#"
let pkgs = { hello = 1; gcc = 2; };
in with pkgs; [ hello ]
#               ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"hello"),
            "should suggest hello from with, got: {names:?}"
        );
        assert!(
            names.contains(&"gcc"),
            "should suggest gcc from with, got: {names:?}"
        );
        // Outer let-bindings should also be visible.
        assert!(
            names.contains(&"pkgs"),
            "should suggest pkgs from outer let, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // Inherit completion
    // ------------------------------------------------------------------

    #[test]
    fn inherit_plain() {
        let src = r#"
let x = 1; y = 2;
in { inherit x ; }
#            ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        // `x` is already inherited — filtered out; `y` is still available.
        assert!(
            !names.contains(&"x"),
            "should NOT suggest x (already inherited), got: {names:?}"
        );
        assert!(names.contains(&"y"), "should suggest y, got: {names:?}");
    }

    #[test]
    fn inherit_from_expr() {
        let src = r#"
let lib = { id = 1; map = 2; };
in { inherit (lib) id ; }
#                  ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        // `id` is already inherited from lib — filtered out.
        assert!(
            !names.contains(&"id"),
            "should NOT suggest id (already inherited), got: {names:?}"
        );
        assert!(names.contains(&"map"), "should suggest map, got: {names:?}");
    }

    #[test]
    fn inherit_from_filters_existing() {
        let src = r#"
let lib = { id = 1; map = 2; filter = 3; };
in { inherit (lib) id filter ; }
#                      ^1
"#;
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        // `id` and `filter` are already inherited — should be filtered out.
        assert!(
            !names.contains(&"id"),
            "should NOT suggest id (already inherited), got: {names:?}"
        );
        assert!(
            !names.contains(&"filter"),
            "should NOT suggest filter (already inherited), got: {names:?}"
        );
        assert!(names.contains(&"map"), "should suggest map, got: {names:?}");
    }
}
