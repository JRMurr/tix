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
// 2. **Attrpath key completion** — cursor after `.` in an attrset key position
//    (e.g. `programs.` inside a NixOS module body). Finds the module's config
//    type from the root lambda's pattern fields and suggests nested option paths.
//
// 3. **Callsite attrset completion** — cursor inside `{ }` that is a function
//    argument (e.g. `mkDerivation { | }`). Looks up the function's parameter
//    type and suggests fields not already present.
//
// 4. **Inherit completion** — cursor inside `inherit ...;`. For plain `inherit`,
//    suggests names from the enclosing scope. For `inherit (expr)`, suggests
//    fields from the expression's type.
//
// 5. **Identifier completion** — catch-all for any expression position. Suggests
//    all visible names (let bindings, lambda params, `with` env fields, builtins).

use std::collections::BTreeMap;

use lang_ast::nameres::{self, ResolveResult};
use lang_ast::{AstPtr, Expr, ExprId, NameKind};
use lang_check::aliases::DocIndex;
use lang_ty::{OutputTy, TyRef};
use rowan::ast::AstNode;
use smol_str::SmolStr;
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionResponse, Documentation, MarkupContent,
    MarkupKind, Position,
};

use crate::convert::LineIndex;
use crate::state::FileSnapshot;

/// Entry point: try to produce completions for the given cursor position.
///
/// `line_index` and `root` may come from a fresher parse than `analysis` —
/// when the user types a trigger character like `.`, the editor sends
/// completion before the debounced analysis finishes. The caller can re-parse
/// the latest text to get a fresh tree+LineIndex while still using the stale
/// `analysis` for type inference results (which remain valid because the base
/// expression's text range hasn't changed).
pub fn completion(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
    docs: &DocIndex,
    line_index: &LineIndex,
) -> Option<CompletionResponse> {
    let inference = analysis.inference_result()?;
    let offset = line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        // left_biased: when cursor is right after `.`, we want the `.` token itself
        // (not the whitespace/ident to the right).
        .left_biased()?;

    log::debug!(
        "completion: pos={pos:?}, token={:?} {:?}, doc_field_docs={}, doc_decl_docs={}",
        token.kind(),
        token.text(),
        docs.field_docs_count(),
        docs.decl_docs_count(),
    );

    // Try dot completion first (cursor right after `.` in a Select).
    if let Some(items) = try_dot_completion(analysis, inference, &token, docs) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Try attrpath key completion (cursor after `.` in an attrset key like
    // `programs.` inside a NixOS module return body).
    if let Some(items) = try_attrpath_key_completion(analysis, inference, &token, docs) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Try callsite attrset completion (cursor inside `{ }` argument).
    if let Some(items) = try_callsite_completion(analysis, inference, &token, docs) {
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

/// Degraded completion path used when analysis hasn't caught up to the latest
/// edit (pending_text exists). Tries dot completion and callsite attrset
/// completion via name-text lookup first (safe because the definition hasn't
/// changed, only ranges shifted), then falls back to identifier completion
/// from scope info.
///
/// `root` and `line_index` come from a fresh parse of the latest text, while
/// `analysis` is from the previous (stale) analysis. Scope structure is
/// structural and tolerates small edits, so identifier suggestions remain
/// useful even when type info is slightly behind.
pub fn syntax_only_completion(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
    line_index: &LineIndex,
) -> Option<CompletionResponse> {
    let offset = line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .left_biased()?;

    // Try dot completion first — uses name-text lookup against stale analysis,
    // no source_map needed. Safe because the definition's type hasn't changed,
    // only the cursor position / ranges have shifted.
    if let Some(items) = try_syntax_only_dot_completion(analysis, &token) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Try callsite attrset completion — same name-text lookup strategy.
    // Handles `f { | }` when analysis is stale.
    if let Some(items) = try_syntax_only_callsite_completion(analysis, &token) {
        if !items.is_empty() {
            return Some(CompletionResponse::Array(items));
        }
    }

    // Fallback: identifier completion from scope chain.
    let scope_id = scope_at_token(analysis, &token)?;
    let visible = collect_visible_names_no_inference(analysis, scope_id);

    let items: Vec<CompletionItem> = visible
        .into_iter()
        .map(|(name, ty)| CompletionItem {
            label: name.to_string(),
            kind: Some(completion_kind_for_ty(ty.as_ref())),
            detail: ty.as_ref().map(|t| format!("{t}")),
            ..Default::default()
        })
        .collect();

    if items.is_empty() {
        None
    } else {
        Some(CompletionResponse::Array(items))
    }
}

/// Dot completion for the degraded (syntax-only) path.
///
/// When analysis is stale but the user typed `.` on a trigger, we can still
/// provide dot completion by looking up the base identifier's type by name
/// text rather than by source_map range. This avoids the range-mismatch
/// problem that occurs when the fresh tree has shifted offsets (e.g. a new
/// line was inserted before `lib.`).
///
/// Strategy:
/// 1. Guard: token must be TOKEN_DOT
/// 2. Find the Select node in the fresh tree
/// 3. Extract the base identifier text (e.g. "lib")
/// 4. Search stale analysis.syntax.module.names() for a NameId with matching text
/// 5. Look up its type in inference.name_ty_map
/// 6. Collect typed segments and resolve through them
/// 7. Return field completion items (without doc context — acceptable degradation)
fn try_syntax_only_dot_completion(
    analysis: &FileSnapshot,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    use rnix::SyntaxKind;

    if token.kind() != SyntaxKind::TOKEN_DOT {
        return None;
    }

    let inference = analysis.inference_result()?;

    // Walk ancestors from the token's parent to find a Select node in the fresh tree.
    let node = token.parent()?;
    let select_node = node.ancestors().find_map(rnix::ast::Select::cast)?;

    // Extract the base expression's identifier text. We only handle simple
    // identifier bases (e.g. `lib` in `lib.strings.`), not complex expressions.
    let base_expr = select_node.expr()?;
    let base_name_text = extract_ident_text(&base_expr)?;

    // Search the stale module's names for one with matching text that has
    // attrset fields in its type. This is the name-text lookup that avoids
    // needing source_map ranges.
    let base_ty = find_name_type_by_text(analysis, inference, &base_name_text)?;

    let cursor_offset = token.text_range().end();
    let typed_segments = collect_typed_segments(&select_node, cursor_offset);

    log::debug!(
        "syntax_only_dot_completion: base={base_name_text}, base_ty={base_ty}, segments={typed_segments:?}"
    );

    let resolved_ty = resolve_through_segments(&base_ty, &typed_segments).unwrap_or(base_ty);

    // No doc context in the degraded path — acceptable tradeoff.
    let fields = collect_attrset_fields(&resolved_ty);
    Some(fields_to_completion_items(&fields, None))
}

/// Callsite attrset completion for the degraded (syntax-only) path.
///
/// When analysis is stale but the user is typing inside `f { | }`, the fresh
/// tree has the Apply+AttrSet structure but the source_map can't resolve the
/// function's ExprId (ranges have shifted). Instead, we extract the function's
/// name text from the fresh tree and look it up by name in the stale analysis
/// — the same strategy as `try_syntax_only_dot_completion`.
///
/// Existing fields are collected directly from the fresh rnix AttrSet node
/// (no source_map needed) so filtering works even when the attrset is new.
fn try_syntax_only_callsite_completion(
    analysis: &FileSnapshot,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<Vec<CompletionItem>> {
    let inference = analysis.inference_result()?;

    let node = token.parent()?;

    // Find the enclosing AttrSet syntax node.
    let attrset_node = node.ancestors().find_map(rnix::ast::AttrSet::cast)?;

    // The AttrSet's parent must be an Apply node (i.e. it's a function argument).
    let apply_node = attrset_node
        .syntax()
        .parent()
        .and_then(rnix::ast::Apply::cast)?;

    // Extract the function's identifier text from the fresh tree.
    let fun_expr = apply_node.lambda()?;
    let fun_name_text = extract_ident_text(&fun_expr)?;

    // Look up the function's type by name text against the stale analysis.
    let fun_ty = find_name_type_by_text(analysis, inference, &fun_name_text)?;

    log::debug!("syntax_only_callsite_completion: fun={fun_name_text}, fun_ty={fun_ty}");

    // Extract the parameter type from the function type.
    let param_ty = extract_lambda_param(&fun_ty)?;

    // Get expected fields from the parameter type.
    let expected_fields = collect_attrset_fields(&param_ty);
    if expected_fields.is_empty() {
        return None;
    }

    // Collect fields already present in the attrset literal directly from the
    // fresh rnix tree — no source_map needed.
    let existing = collect_existing_fields_from_tree(&attrset_node);

    log::debug!(
        "syntax_only_callsite_completion: expected={:?}, existing={existing:?}",
        expected_fields.keys().collect::<Vec<_>>()
    );

    // Return only the fields that haven't been written yet.
    let remaining: BTreeMap<SmolStr, TyRef> = expected_fields
        .into_iter()
        .filter(|(k, _)| !existing.contains(k))
        .collect();

    // No doc context in the degraded path — acceptable tradeoff.
    Some(fields_to_completion_items(&remaining, None))
}

/// Collect field names already present in an attrset literal by walking the
/// fresh rnix tree directly. Unlike `collect_existing_fields`, this does not
/// need the source_map — it reads ident tokens from `AttrpathValue` children.
fn collect_existing_fields_from_tree(attrset_node: &rnix::ast::AttrSet) -> Vec<SmolStr> {
    use rnix::ast::HasEntry;

    attrset_node
        .attrpath_values()
        .filter_map(|apv: rnix::ast::AttrpathValue| {
            // Only consider simple single-segment attrpaths (the common case
            // for function call arguments like `{ name = "x"; src = ./.; }`).
            let attrpath = apv.attrpath()?;
            let mut attrs = attrpath.attrs();
            let first = attrs.next()?;
            // Multi-segment paths (e.g. `a.b = ...`) are not callsite fields.
            if attrs.next().is_some() {
                return None;
            }
            match first {
                rnix::ast::Attr::Ident(ident) => {
                    ident.ident_token().map(|t| SmolStr::from(t.text()))
                }
                _ => None,
            }
        })
        .collect()
}

/// Extract the identifier text from a simple expression node (Ident).
/// Returns None for complex expressions like function calls or nested selects.
fn extract_ident_text(expr: &rnix::ast::Expr) -> Option<SmolStr> {
    match expr {
        rnix::ast::Expr::Ident(ident) => ident.ident_token().map(|t| SmolStr::from(t.text())),
        _ => None,
    }
}

/// Find a name's type by searching the stale module for a NameId with matching
/// text, then looking up its type in inference results.
///
/// Prefers names that have attrset fields (the common case for dot completion).
/// Falls back to lambda param extraction for PatField/Param names.
fn find_name_type_by_text(
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    name_text: &str,
) -> Option<OutputTy> {
    let mut best: Option<OutputTy> = None;

    for (name_id, name) in analysis.syntax.module.names() {
        if name.text != name_text {
            continue;
        }

        // Try direct name_ty_map lookup.
        if let Some(ty) = inference.name_ty_map.get(name_id) {
            if !collect_attrset_fields(ty).is_empty() {
                return Some(ty.clone());
            }
            // Remember this as a fallback even if it has no attrset fields.
            if best.is_none() {
                best = Some(ty.clone());
            }
        }

        // For lambda params, extract param type from the enclosing Lambda.
        if matches!(name.kind, NameKind::Param | NameKind::PatField) {
            if let Some(&lambda_expr_id) = analysis.syntax.module_indices.param_to_lambda.get(&name_id) {
                if let Some(lambda_ty) = inference.expr_ty_map.get(lambda_expr_id) {
                    if let Some(param_ty) = extract_lambda_param(lambda_ty) {
                        let resolved = if name.kind == NameKind::PatField {
                            // PatField: extract the specific field from the param type.
                            let fields = collect_attrset_fields(&param_ty);
                            fields.get(&name.text).map(|f| (*f.0).clone())
                        } else {
                            Some(param_ty)
                        };
                        if let Some(ref ty) = resolved {
                            if !collect_attrset_fields(ty).is_empty() {
                                return resolved;
                            }
                            if best.is_none() {
                                best = resolved;
                            }
                        }
                    }
                }
            }
        }
    }

    best
}

// ==============================================================================
// Dot completion: `lib.` or `lib.strings.`
// ==============================================================================

fn try_dot_completion(
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
    docs: &DocIndex,
) -> Option<Vec<CompletionItem>> {
    // Walk ancestors from the token's parent to find a Select node.
    let node = token.parent()?;
    let select_node = node.ancestors().find_map(rnix::ast::Select::cast)?;

    // Get the base expression of the Select (e.g. `lib` in `lib.strings.x`).
    let base_expr = select_node.expr()?;
    let base_ptr = AstPtr::new(base_expr.syntax());
    let base_expr_id = analysis.syntax.source_map.expr_for_node(base_ptr)?;

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

    // Extract the alias name from the base type for doc lookups (e.g.
    // "NixosConfig" from Named("NixosConfig", {...})). Must happen before
    // the unwrap_or below moves base_ty.
    let alias = extract_alias_name(&base_ty).cloned();

    // Walk through the typed segments to resolve the nested type.
    // If segment resolution fails (e.g. the type doesn't have the expected
    // field, or error-recovery injected a bogus segment), fall back to just
    // showing the base type's fields.
    let resolved_ty = resolve_through_segments(&base_ty, &typed_segments).unwrap_or(base_ty);

    let doc_ctx = alias
        .as_ref()
        .map(|a| (docs, a.as_str(), typed_segments.as_slice()));

    // Extract fields from the resolved type and build completion items.
    let fields = collect_attrset_fields(&resolved_ty);
    Some(fields_to_completion_items(&fields, doc_ctx))
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
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    base_expr_id: ExprId,
) -> Option<OutputTy> {
    // Primary: direct expr_ty_map lookup.
    if let Some(ty) = inference.expr_ty_map.get(base_expr_id) {
        if !collect_attrset_fields(ty).is_empty() {
            return Some(ty.clone());
        }
    }

    // Fallback: resolve through name resolution.
    let resolve_result = analysis.syntax.name_res.get(base_expr_id)?;
    let name_id = match resolve_result {
        ResolveResult::Definition(name_id) => *name_id,
        _ => {
            // For `with` expressions, try the expr_ty_map type even if it
            // has no attrset fields (it may still be useful after segment resolution).
            return inference.expr_ty_map.get(base_expr_id).cloned();
        }
    };

    // Check name_ty_map for a concrete type.
    if let Some(name_ty) = inference.name_ty_map.get(name_id) {
        if !collect_attrset_fields(name_ty).is_empty() {
            return Some(name_ty.clone());
        }
    }

    // For lambda parameters, extract the param type from the enclosing
    // Lambda's canonicalized type.
    let name = &analysis.syntax.module[name_id];
    if matches!(name.kind, NameKind::Param | NameKind::PatField) {
        if let Some(&lambda_expr_id) = analysis.syntax.module_indices.param_to_lambda.get(&name_id) {
            if let Some(lambda_ty) = inference.expr_ty_map.get(lambda_expr_id) {
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
    inference.expr_ty_map.get(base_expr_id).cloned()
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

use crate::ty_nav::{
    collect_attrset_fields, collect_parent_attrpath_context, extract_alias_name,
    extract_lambda_param, get_module_config_type, get_str_literal, resolve_through_segments,
};

// ==============================================================================
// Attrpath key completion: `programs.` in NixOS module return body
// ==============================================================================
//
// Inside a NixOS module like `{ config, ... }: { programs.steam.enable = true; }`,
// the return attrset's keys are option paths. rnix parses `programs.` as an
// incomplete AttrpathValue (not a Select expression), so dot completion doesn't
// trigger. This strategy detects the pattern, finds the config type from the
// root lambda's pattern fields, and suggests the next level of option keys.

fn try_attrpath_key_completion(
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
    docs: &DocIndex,
) -> Option<Vec<CompletionItem>> {
    use rnix::SyntaxKind;

    // Guard: token must be a dot inside an attrpath key.
    if token.kind() != SyntaxKind::TOKEN_DOT {
        return None;
    }

    // Walk ancestors from the token's parent to find an Attrpath node.
    let node = token.parent()?;
    let attrpath_node = node.ancestors().find_map(rnix::ast::Attrpath::cast)?;

    // The Attrpath must be inside an AttrpathValue (not a Select — that's dot
    // completion). If the parent is a Select, bail out.
    let parent = attrpath_node.syntax().parent()?;
    if rnix::ast::Select::can_cast(parent.kind()) {
        return None;
    }
    let _attrpath_value_node = rnix::ast::AttrpathValue::cast(parent)?;

    // Find the enclosing AttrSet.
    let attrset_node = _attrpath_value_node
        .syntax()
        .parent()
        .and_then(rnix::ast::AttrSet::cast)?;

    // Collect segments from the current attrpath before the cursor.
    let cursor_offset = token.text_range().end();
    let current_segments =
        crate::ty_nav::collect_attrpath_segments(&attrpath_node, cursor_offset, false);

    // Collect parent context segments from enclosing AttrpathValue/AttrSet
    // nesting. For `{ services.openssh = { enable. } }`, if we're at `enable.`,
    // the parent context is ["services", "openssh"].
    let parent_segments = collect_parent_attrpath_context(&attrset_node);

    // Full path = parent context + current segments.
    let mut full_path = parent_segments;
    full_path.extend(current_segments);

    log::debug!("attrpath_key_completion: full_path={full_path:?}");

    // Find the module config type: scan the root lambda's pattern fields for
    // one whose type contains the first path segment as a field.
    let first_segment = full_path.first()?;
    let config_ty = get_module_config_type(
        analysis,
        inference,
        first_segment,
        &analysis.syntax.context_arg_types,
    )?;

    // Extract the alias name before unwrap_or moves config_ty.
    let alias = extract_alias_name(&config_ty).cloned();

    log::debug!(
        "attrpath_key_completion: config_ty alias={:?}, full_path={:?}",
        alias,
        full_path,
    );

    // Walk the config type through the full path.
    let resolved_ty = resolve_through_segments(&config_ty, &full_path).unwrap_or(config_ty);

    let doc_ctx = alias
        .as_ref()
        .map(|a| (docs, a.as_str(), full_path.as_slice()));

    // Extract fields and return completion items.
    let fields = collect_attrset_fields(&resolved_ty);
    Some(fields_to_completion_items(&fields, doc_ctx))
}

// ==============================================================================
// Callsite attrset completion: `f { | }`
// ==============================================================================

fn try_callsite_completion(
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
    docs: &DocIndex,
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

    // Try source_map lookup first (precise, works when analysis is current).
    // Fall back to name-text lookup when analysis is stale (source_map can't
    // find the Apply node from the fresh tree).
    let fun_ty = match analysis
        .syntax
        .source_map
        .expr_for_node(AstPtr::new(fun_expr.syntax()))
    {
        Some(fun_expr_id) => inference.expr_ty_map.get(fun_expr_id)?.clone(),
        None => {
            let fun_name_text = extract_ident_text(&fun_expr)?;
            find_name_type_by_text(analysis, inference, &fun_name_text)?
        }
    };

    log::debug!("callsite_completion: fun_ty={fun_ty}");

    // Extract the parameter type from the function type.
    let param_ty = extract_lambda_param(&fun_ty)?;

    // Get expected fields from the parameter type.
    let expected_fields = collect_attrset_fields(&param_ty);
    if expected_fields.is_empty() {
        return None;
    }

    // Collect fields already present in the attrset literal to filter them out.
    // Try source_map first; fall back to tree walk when analysis is stale.
    let existing = {
        let from_map = collect_existing_fields(analysis, &attrset_node);
        if from_map.is_empty() {
            collect_existing_fields_from_tree(&attrset_node)
        } else {
            from_map
        }
    };

    log::debug!(
        "callsite_completion: expected={:?}, existing={existing:?}",
        expected_fields.keys().collect::<Vec<_>>()
    );

    // Return only the fields that haven't been written yet.
    let remaining: BTreeMap<SmolStr, TyRef> = expected_fields
        .into_iter()
        .filter(|(k, _)| !existing.contains(k))
        .collect();

    // Try to surface docs for the parameter type's alias (e.g. Derivation fields).
    let alias = extract_alias_name(&param_ty);
    let doc_ctx = alias.map(|a| (docs, a.as_str(), &[] as &[SmolStr]));

    Some(fields_to_completion_items(&remaining, doc_ctx))
}

/// Collect field names already present in an attrset literal, using the lowered
/// AST (Bindings) rather than re-parsing rnix. We look up the AttrSet's ExprId
/// in the source map and read its static binding names from the Module.
fn collect_existing_fields(
    analysis: &FileSnapshot,
    attrset_node: &rnix::ast::AttrSet,
) -> Vec<SmolStr> {
    let ptr = AstPtr::new(attrset_node.syntax());
    let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) else {
        return Vec::new();
    };

    match &analysis.syntax.module[expr_id] {
        Expr::AttrSet { bindings, .. } => bindings
            .statics
            .iter()
            .map(|(name_id, _)| analysis.syntax.module[*name_id].text.clone())
            .collect(),
        _ => Vec::new(),
    }
}

// ==============================================================================
// Inherit completion: `inherit ▊;` and `inherit (expr) ▊;`
// ==============================================================================

fn try_inherit_completion(
    analysis: &FileSnapshot,
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
        let expr_id = analysis.syntax.source_map.expr_for_node(expr_ptr)?;
        let ty = inference.expr_ty_map.get(expr_id)?;
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
                analysis.syntax.source_map.expr_for_node(ptr)
            } else {
                None
            }
        })?;

        let scope_id = analysis.syntax.scopes.scope_for_expr(enclosing_expr_id)?;
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
    analysis: &FileSnapshot,
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
    analysis: &FileSnapshot,
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
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            if let Some(scope_id) = analysis.syntax.scopes.scope_for_expr(expr_id) {
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
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    scope_id: nameres::ScopeId,
) -> BTreeMap<SmolStr, Option<OutputTy>> {
    let mut result: BTreeMap<SmolStr, Option<OutputTy>> = BTreeMap::new();

    for scope_data in analysis.syntax.scopes.ancestors(scope_id) {
        if let Some(defs) = scope_data.as_definitions() {
            for (name, name_id) in defs {
                result
                    .entry(name.clone())
                    .or_insert_with(|| inference.name_ty_map.get(*name_id).cloned());
            }
        } else if let Some(with_expr_id) = scope_data.as_with() {
            // The With expression's env is the first child.
            if let Expr::With { env, .. } = &analysis.syntax.module[with_expr_id] {
                if let Some(env_ty) = inference.expr_ty_map.get(*env) {
                    for (field_name, field_ty) in collect_attrset_fields(env_ty) {
                        result
                            .entry(field_name)
                            .or_insert_with(|| Some((*field_ty.0).clone()));
                    }
                }
            }
        }
    }

    // Append builtins at lowest priority, sourced from the authoritative list
    // in nameres. Extras: `builtins` namespace and keyword-like literals.
    for name in lang_ast::nameres::GLOBAL_BUILTIN_NAMES {
        result.entry(SmolStr::from(*name)).or_insert(None);
    }
    for name in ["builtins", "true", "false", "null"] {
        result.entry(SmolStr::from(name)).or_insert(None);
    }

    result
}

/// Like `collect_visible_names` but doesn't require inference results.
///
/// Uses inference types opportunistically when available (from stale analysis),
/// but produces results even without them. Used by `syntax_only_completion`
/// for the degraded pending_text path.
fn collect_visible_names_no_inference(
    analysis: &FileSnapshot,
    scope_id: nameres::ScopeId,
) -> BTreeMap<SmolStr, Option<OutputTy>> {
    let mut result: BTreeMap<SmolStr, Option<OutputTy>> = BTreeMap::new();
    let inference = analysis.inference_result();

    for scope_data in analysis.syntax.scopes.ancestors(scope_id) {
        if let Some(defs) = scope_data.as_definitions() {
            for (name, name_id) in defs {
                result.entry(name.clone()).or_insert_with(|| {
                    inference.and_then(|inf| inf.name_ty_map.get(*name_id).cloned())
                });
            }
        } else if let Some(with_expr_id) = scope_data.as_with() {
            if let Some(inf) = inference {
                if let Expr::With { env, .. } = &analysis.syntax.module[with_expr_id] {
                    if let Some(env_ty) = inf.expr_ty_map.get(*env) {
                        for (field_name, field_ty) in collect_attrset_fields(env_ty) {
                            result
                                .entry(field_name)
                                .or_insert_with(|| Some((*field_ty.0).clone()));
                        }
                    }
                }
            }
        }
    }

    // Append builtins at lowest priority.
    for name in lang_ast::nameres::GLOBAL_BUILTIN_NAMES {
        result.entry(SmolStr::from(*name)).or_insert(None);
    }
    for name in ["builtins", "true", "false", "null"] {
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

// ==============================================================================
// CompletionItem construction
// ==============================================================================

/// Build completion items from attrset fields, optionally enriching each item
/// with doc comments from the DocIndex.
///
/// `doc_ctx` is `Some((docs, alias_name, path_prefix))` when we know which type
/// alias the fields belong to and the path prefix leading to them. For example,
/// completing `programs.` in a NixOS module gives alias "NixosConfig" with
/// prefix `["programs"]`, so field "steam" looks up
/// `field_doc("NixosConfig", &["programs", "steam"])`.
fn fields_to_completion_items(
    fields: &BTreeMap<SmolStr, TyRef>,
    doc_ctx: Option<(&DocIndex, &str, &[SmolStr])>,
) -> Vec<CompletionItem> {
    fields
        .iter()
        .map(|(name, ty)| {
            let documentation = doc_ctx.and_then(|(docs, alias, prefix)| {
                let mut path: Vec<SmolStr> = prefix.to_vec();
                path.push(name.clone());
                docs.field_doc(alias, &path).map(|d| {
                    Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: d.to_string(),
                    })
                })
            });

            // Store alias + field path in `data` for completionItem/resolve.
            // This lets the client lazily fetch documentation on highlight.
            let data = doc_ctx.map(|(_, alias, prefix)| {
                let mut path: Vec<&str> = prefix.iter().map(|s| s.as_str()).collect();
                path.push(name.as_str());
                serde_json::json!({ "alias": alias, "path": path })
            });

            CompletionItem {
                label: name.to_string(),
                kind: Some(CompletionItemKind::FIELD),
                detail: Some(format!("{ty}")),
                documentation,
                data,
                ..Default::default()
            }
        })
        .collect()
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    use crate::project_config::{ContextConfig, ProjectConfig};
    use crate::state::AnalysisState;
    use crate::test_util::{find_offset, parse_markers, TestAnalysis};
    use indoc::indoc;
    use lang_check::aliases::TypeAliasRegistry;

    /// Analyze source and get completions at a given byte offset.
    fn complete_at(src: &str, offset: u32) -> Vec<CompletionItem> {
        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();
        let pos = analysis.syntax.line_index.position(offset);
        let docs = DocIndex::new();

        match completion(&analysis, pos, &t.root, &docs, &analysis.syntax.line_index) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        }
    }

    fn labels(items: &[CompletionItem]) -> Vec<&str> {
        items.iter().map(|i| i.label.as_str()).collect()
    }

    /// Run completions at all marker positions. Returns marker → completions.
    fn complete_at_markers(src: &str) -> BTreeMap<u32, Vec<CompletionItem>> {
        let markers = parse_markers(src);
        assert!(!markers.is_empty(), "no markers found in source");

        let t = TestAnalysis::new(src);
        let analysis = t.snapshot();
        let docs = DocIndex::new();

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = analysis.syntax.line_index.position(offset);
                let items = match completion(&analysis, pos, &t.root, &docs, &analysis.syntax.line_index) {
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
        let src = indoc! {r#"
            let lib = { x = 1; y = "hello"; };
            in lib.
            #      ^1
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(names.contains(&"x"), "should complete x, got: {names:?}");
        assert!(names.contains(&"y"), "should complete y, got: {names:?}");
    }

    #[test]
    fn dot_completion_nested() {
        let src = indoc! {r#"
            let lib = { strings = { concat = 1; sep = 2; }; };
            in lib.strings.
            #              ^1
        "#};
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
        let src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { }
            #     ^1
        "#};
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
        let src = indoc! {r#"
            let pkgs = { hello = 1; gcc = 2; };
            in [ pkgs. ]
            #         ^1
        "#};
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
        let src = indoc! {r#"
            let f = pkgs: pkgs;
                r = f { hello = 1; gcc = 2; };
            in r.
            #    ^1
        "#};
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

    /// Regression test: dot completion works when using a fresh parse tree
    /// against stale analysis results. This simulates the real LSP scenario
    /// where the user types `.` (a trigger character) and the editor sends
    /// completion before the debounced analysis finishes.
    #[test]
    fn dot_completion_with_stale_analysis() {
        use crate::convert::LineIndex;

        // Step 1: Analyze the file WITHOUT the trailing dot.
        let stale_src = indoc! {r#"
            let lib = { x = 1; y = "hello"; };
            in lib
        "#};
        let t = TestAnalysis::new(stale_src);
        let stale_analysis = t.snapshot();

        // Step 2: The user types `.` — fresh text has `lib.` but analysis
        // is still from the pre-dot version.
        let fresh_src = indoc! {r#"
            let lib = { x = 1; y = "hello"; };
            in lib.
        "#};
        let fresh_root = rnix::Root::parse(fresh_src).tree();
        let fresh_line_index = LineIndex::new(fresh_src);

        // Cursor is right after the `.`
        let dot_offset = fresh_src.rfind('.').unwrap() as u32 + 1;
        let pos = fresh_line_index.position(dot_offset);
        let docs = DocIndex::new();

        let items = match completion(&stale_analysis, pos, &fresh_root, &docs, &fresh_line_index) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        };
        let names = labels(&items);
        assert!(
            names.contains(&"x"),
            "stale analysis + fresh parse should complete x, got: {names:?}"
        );
        assert!(
            names.contains(&"y"),
            "stale analysis + fresh parse should complete y, got: {names:?}"
        );
    }

    #[test]
    fn callsite_completion_filters_existing() {
        let src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { name = "x"; }
            #                  ^1
        "#};
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

    #[test]
    fn callsite_completion_with_defaults() {
        // Regression test: functions with `? null` defaults should still
        // offer callsite completion for all pattern fields.
        let src = indoc! {r#"
            let
              f = { args, name, script, pasta ? null, paths ? null }: name;
            in f { }
            #      ^1
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"args"),
            "should complete args, got: {names:?}"
        );
        assert!(
            names.contains(&"name"),
            "should complete name, got: {names:?}"
        );
        assert!(
            names.contains(&"script"),
            "should complete script, got: {names:?}"
        );
        assert!(
            names.contains(&"pasta"),
            "should complete pasta, got: {names:?}"
        );
        assert!(
            names.contains(&"paths"),
            "should complete paths, got: {names:?}"
        );
    }

    /// Callsite completion when the call is in a let-binding value (not body).
    /// This matches the real-world pattern: `foo = bubblewrap_helper { };`.
    #[test]
    fn callsite_completion_in_let_binding() {
        let src = indoc! {r#"
            let
              f = { args, name, script, pasta ? null, paths ? null }: name;
              foo = f { }
              #        ^1
            ;
            in foo
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"args"),
            "should complete args in let binding, got: {names:?}"
        );
        assert!(
            names.contains(&"name"),
            "should complete name in let binding, got: {names:?}"
        );
    }

    /// Regression test: callsite completion works when using a fresh parse
    /// tree against stale analysis results. This simulates the real LSP
    /// scenario where the user adds `f { }` and the editor sends completion
    /// before the debounced analysis finishes.
    #[test]
    fn callsite_completion_with_stale_analysis() {
        use crate::convert::LineIndex;

        // Step 1: Analyze the file WITHOUT the callsite.
        let stale_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f
        "#};
        let t = TestAnalysis::new(stale_src);
        let stale_analysis = t.snapshot();

        // Step 2: The user types ` { }` — fresh text has the callsite but
        // analysis is still from the pre-callsite version.
        let fresh_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { }
            #     ^1
        "#};
        let fresh_root = rnix::Root::parse(fresh_src).tree();
        let fresh_line_index = LineIndex::new(fresh_src);
        let markers = parse_markers(fresh_src);
        let docs = DocIndex::new();

        let pos = fresh_line_index.position(markers[&1]);
        let items = match completion(&stale_analysis, pos, &fresh_root, &docs, &fresh_line_index) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        };
        let names = labels(&items);
        assert!(
            names.contains(&"name"),
            "stale analysis + fresh callsite should complete name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "stale analysis + fresh callsite should complete src, got: {names:?}"
        );
    }

    /// Regression test: callsite completion with stale analysis correctly
    /// filters out fields already present in the fresh attrset literal.
    #[test]
    fn callsite_completion_with_stale_analysis_filters_existing() {
        use crate::convert::LineIndex;

        let stale_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f
        "#};
        let t = TestAnalysis::new(stale_src);
        let stale_analysis = t.snapshot();

        let fresh_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { name = "x"; }
            #                  ^1
        "#};
        let fresh_root = rnix::Root::parse(fresh_src).tree();
        let fresh_line_index = LineIndex::new(fresh_src);
        let markers = parse_markers(fresh_src);
        let docs = DocIndex::new();

        let pos = fresh_line_index.position(markers[&1]);
        let items = match completion(&stale_analysis, pos, &fresh_root, &docs, &fresh_line_index) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        };
        let names = labels(&items);
        assert!(
            !names.contains(&"name"),
            "should NOT complete already-present name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "stale analysis + fresh callsite should complete src, got: {names:?}"
        );
    }

    /// Regression test: callsite completion for a complex function whose body
    /// contains many let-bindings, if-else chains, and nested lambdas. This
    /// mirrors the real-world `bubblewrap_helper` from `test/null_default.nix`
    /// where the simple `callsite_completion_in_let_binding` test passes but
    /// the full file fails.
    #[test]
    fn callsite_completion_complex_function() {
        // Simplified version of the real file — uses the same structure
        // (top-level pattern lambda, lib bindings, complex function body)
        // but without external nixpkgs dependencies.
        let src = indoc! {r#"
            {
              pkgs,
            }:
            let
              lib = pkgs.lib;

              bubblewrap_helper =
                {
                  args,
                  name,
                  script,
                  pasta ? null,
                  paths ? null,
                }:
                let
                  inner_script = pkgs.writeShellScript name script;

                  bindTypes = {
                    ro = "--ro-bind";
                    ro_maybe = "--ro-bind-try";
                    rw = "--bind";
                    rw_maybe = "--bind-try";
                    dev_maybe = "--dev-bind-try";
                  };

                  renderArg =
                    arg':
                    let
                      arg = if builtins.isString arg' then { escaped = arg'; } else arg';
                    in
                    if !(arg.cond or true) then
                      ""
                    else if arg ? escaped then
                      lib.escapeShellArg arg.escaped
                    else if arg ? unescaped then
                      arg.unescaped
                    else if arg ? tmpfs then
                      "--tmpfs ${arg.tmpfs}"
                    else if arg ? setenv then
                      "--setenv ${lib.escapeShellArg arg.setenv} ${lib.escapeShellArg arg.value}"
                    else
                      let
                        kind = lib.findFirst (k: arg ? ${k}) null (builtins.attrNames bindTypes);
                      in
                      if kind == null then
                        builtins.throw "Unsupported bwrap argument: ${builtins.toJSON arg}"
                      else
                        "${bindTypes.${kind}} ${arg.src or arg.${kind}} ${arg.${kind}}";
                  bwrap_args = lib.concatMapStringsSep " " renderArg args;

                  pastaFlags = lib.optionalString (pasta != null) (
                    let
                      hasTcp = pasta.tcpForward or [ ] != [ ];
                      hasUdp = pasta.udpForward or [ ] != [ ];
                      tcpFlags =
                        if hasTcp then "-t none -T ${lib.concatMapStringsSep "," builtins.toString pasta.tcpForward}" else "-t none";
                      udpFlags =
                        if hasUdp then "-u none -U ${lib.concatMapStringsSep "," builtins.toString pasta.udpForward}" else "-u none";
                      extraFlags = lib.concatStringsSep " " (pasta.extraFlags or [ ]);
                    in
                    lib.concatStringsSep " " (
                      lib.filter (s: s != "") [
                        tcpFlags
                        udpFlags
                        extraFlags
                      ]
                    )
                  );
                  bwrap_cmd = ''${pkgs.bubblewrap}/bin/bwrap ${bwrap_args} ${inner_script} "$@"'';

                  main_cmd =
                    if pasta == null then
                      bwrap_cmd
                    else
                      "${pkgs.passt}/bin/pasta --config-net ${pastaFlags} -- ${bwrap_cmd}";

                in
                "${main_cmd}";

              foo = bubblewrap_helper { }
              #                        ^1
            ;
            in
            {
              inherit bubblewrap_helper;
            }
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"args"),
            "should complete args for complex function, got: {names:?}"
        );
        assert!(
            names.contains(&"name"),
            "should complete name for complex function, got: {names:?}"
        );
        assert!(
            names.contains(&"script"),
            "should complete script for complex function, got: {names:?}"
        );
        assert!(
            names.contains(&"pasta"),
            "should complete pasta for complex function, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // Identifier completion
    // ------------------------------------------------------------------

    #[test]
    fn identifier_in_let_body() {
        let src = indoc! {r#"
            let x = 1; y = "hello";
            in x
            #  ^1
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(names.contains(&"x"), "should suggest x, got: {names:?}");
        assert!(names.contains(&"y"), "should suggest y, got: {names:?}");
    }

    #[test]
    fn identifier_in_list() {
        let src = indoc! {r#"
            let pkgs = 1;
            in [ pkgs ]
            #    ^1
        "#};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"pkgs"),
            "should suggest pkgs, got: {names:?}"
        );
    }

    #[test]
    fn identifier_includes_builtins() {
        let src = indoc! {r#"
            let x = 1;
            in x
            #  ^1
        "#};
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
        let src = indoc! {r#"
            let f = x: x;
            in f
            #  ^1
        "#};
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
    // Syntax-only completion (degraded path for pending_text)
    // ------------------------------------------------------------------

    /// Analyze stale source, then run syntax_only_completion on fresh source.
    /// Simulates the pending_text scenario: the analysis is from a previous
    /// version of the file, but the fresh text has a new edit.
    fn syntax_only_at_markers(stale_src: &str, fresh_src: &str) -> BTreeMap<u32, Vec<CompletionItem>> {
        let markers = parse_markers(fresh_src);
        assert!(!markers.is_empty(), "no markers found in fresh source");

        let t = TestAnalysis::new(stale_src);
        let stale_analysis = t.snapshot();

        let fresh_root = rnix::Root::parse(fresh_src).tree();
        let fresh_line_index = crate::convert::LineIndex::new(fresh_src);

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = fresh_line_index.position(offset);
                let items = match syntax_only_completion(&stale_analysis, pos, &fresh_root, &fresh_line_index) {
                    Some(CompletionResponse::Array(items)) => items,
                    _ => Vec::new(),
                };
                (num, items)
            })
            .collect()
    }

    #[test]
    fn syntax_only_returns_identifiers() {
        // Stale source doesn't have the trailing expression; fresh source does.
        // syntax_only_completion should still find scope names from the stale
        // analysis's scope chain.
        let stale_src = indoc! {r#"
            let x = 1; y = "hello";
            in x
        "#};
        let fresh_src = indoc! {r#"
            let x = 1; y = "hello";
            in x + y
            #  ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(names.contains(&"x"), "should suggest x, got: {names:?}");
        assert!(names.contains(&"y"), "should suggest y, got: {names:?}");
    }

    #[test]
    fn syntax_only_includes_builtins() {
        let stale_src = "let x = 1; in x";
        let fresh_src = indoc! {r#"
            let x = 1; in x
            #              ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"import"),
            "should include builtins, got: {names:?}"
        );
        assert!(
            names.contains(&"true"),
            "should include true, got: {names:?}"
        );
    }

    #[test]
    fn syntax_only_dot_completion_simple() {
        // When fresh_text has a `.` that triggers completion, syntax_only
        // should provide dot completion via name-text lookup against stale
        // analysis. The definition's type hasn't changed, only the cursor
        // position is new.
        let stale_src = indoc! {r#"
            let lib = { x = 1; y = 2; };
            in lib
        "#};
        let fresh_src = indoc! {r#"
            let lib = { x = 1; y = 2; };
            in lib.
            #      ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"x"),
            "syntax_only should dot-complete x, got: {names:?}"
        );
        assert!(
            names.contains(&"y"),
            "syntax_only should dot-complete y, got: {names:?}"
        );
    }

    #[test]
    fn syntax_only_dot_completion_new_line() {
        // The key scenario: user adds a new line with `lib.`, shifting all
        // ranges. Full completion fails (source_map mismatch), but syntax-only
        // dot completion succeeds via name-text lookup.
        let stale_src = indoc! {r#"
            let lib = { x = 1; y = 2; };
            in lib
        "#};
        let fresh_src = indoc! {r#"
            let lib = { x = 1; y = 2; };
            in
              lib.
            #     ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"x"),
            "syntax_only should dot-complete x on new line, got: {names:?}"
        );
        assert!(
            names.contains(&"y"),
            "syntax_only should dot-complete y on new line, got: {names:?}"
        );
    }

    #[test]
    fn syntax_only_dot_completion_nested() {
        // Nested dot completion: `lib.strings.` on a new line.
        let stale_src = indoc! {r#"
            let lib = { strings = { concat = 1; sep = 2; }; };
            in lib
        "#};
        let fresh_src = indoc! {r#"
            let lib = { strings = { concat = 1; sep = 2; }; };
            in
              lib.strings.
            #             ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"concat"),
            "syntax_only should dot-complete concat, got: {names:?}"
        );
        assert!(
            names.contains(&"sep"),
            "syntax_only should dot-complete sep, got: {names:?}"
        );
    }

    #[test]
    fn syntax_only_callsite_completion() {
        // When the user adds a call site `f { }` that doesn't exist in the
        // stale analysis, full completion fails (source_map can't find the
        // Apply node). The syntax-only path should still provide callsite
        // completion by looking up the function's type by name text.
        let stale_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f
        "#};
        let fresh_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { }
            #     ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"name"),
            "syntax_only should callsite-complete name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "syntax_only should callsite-complete src, got: {names:?}"
        );
    }

    #[test]
    fn syntax_only_callsite_completion_filters_existing() {
        // Existing fields in the fresh tree should be filtered out, even
        // though the attrset doesn't exist in the stale analysis.
        let stale_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f
        "#};
        let fresh_src = indoc! {r#"
            let f = { name, src, ... }: name;
            in f { name = "x"; }
            #                  ^1
        "#};
        let results = syntax_only_at_markers(stale_src, fresh_src);
        let names = labels(&results[&1]);
        assert!(
            !names.contains(&"name"),
            "syntax_only should NOT complete already-present name, got: {names:?}"
        );
        assert!(
            names.contains(&"src"),
            "syntax_only should complete src, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // With-scope completion
    // ------------------------------------------------------------------

    #[test]
    fn with_scope_completion() {
        let src = indoc! {r#"
            let pkgs = { hello = 1; gcc = 2; };
            in with pkgs; [ hello ]
            #               ^1
        "#};
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
        let src = indoc! {r#"
            let x = 1; y = 2;
            in { inherit x ; }
            #            ^1
        "#};
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
        let src = indoc! {r#"
            let lib = { id = 1; map = 2; };
            in { inherit (lib) id ; }
            #                  ^1
        "#};
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
        let src = indoc! {r#"
            let lib = { id = 1; map = 2; filter = 3; };
            in { inherit (lib) id filter ; }
            #                      ^1
        "#};
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

    // ------------------------------------------------------------------
    // Attrpath key completion (NixOS module option paths)
    // ------------------------------------------------------------------

    /// Small context stubs for testing attrpath key completion.
    /// Defines a TestConfig type with nested programs/services structure,
    /// and declares `config :: TestConfig` as a context arg.
    const TEST_CONTEXT_STUBS: &str = indoc! {"
        type TestConfig = {
            programs: {
                steam: { enable: bool, ... },
                firefox: { enable: bool, ... },
                ...
            },
            services: {
                openssh: { enable: bool, port: int, ... },
                ...
            },
            ...
        };
        val config :: TestConfig;
    "};

    /// Run completions at marker positions with context stubs injected.
    ///
    /// Writes the context stubs to a temp directory, configures a
    /// ProjectConfig that matches all .nix files with those stubs, and
    /// runs analysis with context args applied to the root lambda.
    fn complete_at_markers_with_context(
        src: &str,
        context_stubs: &str,
    ) -> BTreeMap<u32, Vec<CompletionItem>> {
        use crate::test_util::ContextTestSetup;

        let markers = parse_markers(src);
        assert!(!markers.is_empty(), "no markers found in source");

        let ctx = ContextTestSetup::new(src, context_stubs);
        let analysis = ctx.snapshot();
        let root = ctx.root();
        let docs = ctx.docs();

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = analysis.syntax.line_index.position(offset);
                let items = match completion(&analysis, pos, &root, docs, &analysis.syntax.line_index) {
                    Some(CompletionResponse::Array(items)) => items,
                    _ => Vec::new(),
                };
                (num, items)
            })
            .collect()
    }

    #[test]
    fn attrpath_key_top_level() {
        // `{ config, ... }: { programs. }` — should suggest fields of
        // TestConfig.programs (steam, firefox).
        let src = indoc! {"
            { config, ... }: { programs. }
            #                           ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam, got: {names:?}"
        );
        assert!(
            names.contains(&"firefox"),
            "should complete firefox, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_nested_path() {
        // `{ config, ... }: { programs.steam. }` — should suggest fields of
        // TestConfig.programs.steam (enable).
        let src = indoc! {"
            { config, ... }: { programs.steam. }
            #                                 ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"enable"),
            "should complete enable, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_services() {
        // Verify that services paths also work.
        let src = indoc! {"
            { config, ... }: { services. }
            #                           ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"openssh"),
            "should complete openssh, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_no_false_positive_without_context() {
        // Without context stubs, attrpath key completion should not fire.
        let src = indoc! {"
            { config, ... }: { programs. }
            #                           ^1
        "};
        let results = complete_at_markers(src);
        let names = labels(&results[&1]);
        // Without context stubs, `config` has no rich type, so `programs`
        // won't resolve to anything and no field completions should appear.
        assert!(
            !names.contains(&"steam"),
            "should NOT suggest steam without context stubs, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_inside_function_call() {
        // NixOS modules commonly wrap the return attrset in `lib.mkIf`:
        //   { config, lib, ... }: { config = lib.mkIf cond { programs. }; }
        // The attrset is an argument to mkIf, not the direct return value.
        // Completion should still find the config type from the root lambda.
        let stubs = indoc! {"
            type TestConfig = {
                programs: {
                    steam: { enable: bool, ... },
                    firefox: { enable: bool, ... },
                    ...
                },
                services: {
                    openssh: { enable: bool, port: int, ... },
                    ...
                },
                ...
            };
            type Lib = { mkIf: bool -> a -> a, ... };
            val config :: TestConfig;
            val lib :: Lib;
        "};
        let src = indoc! {"
            { config, lib, ... }:
            {
              config = lib.mkIf true {
                programs.
            #            ^1
              };
            }
        "};
        let results = complete_at_markers_with_context(src, stubs);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam inside mkIf, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_not_plain_lambda() {
        // A plain lambda (not a pattern) should not trigger attrpath key completion.
        let src = indoc! {"
            config: { programs. }
            #                   ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            !names.contains(&"steam"),
            "should NOT suggest steam for plain lambda param, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_without_destructured_config() {
        // Regression: modules that don't destructure `config` (e.g.
        // `{ pkgs, ... }:`) should still get attrpath key completion via
        // the context_arg_types fallback from tix.toml.
        let src = indoc! {"
            { pkgs, ... }: { programs. }
            #                         ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam via context_arg_types fallback, got: {names:?}"
        );
        assert!(
            names.contains(&"firefox"),
            "should complete firefox via context_arg_types fallback, got: {names:?}"
        );
    }

    #[test]
    fn attrpath_key_plain_attrset_module() {
        // Plain attrset modules (no lambda wrapper) should get attrpath key
        // completion from context_arg_types.
        let src = indoc! {"
            { programs. }
            #          ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam in plain attrset module, got: {names:?}"
        );
        assert!(
            names.contains(&"firefox"),
            "should complete firefox in plain attrset module, got: {names:?}"
        );
    }

    #[test]
    fn no_module_directive_disables_attrpath_key_completion() {
        // A `/** no-module */` comment at the top of the file opts out of
        // module-aware completion, even when context stubs are loaded.
        let src = indoc! {"
            /** no-module */
            { pkgs, ... }: { programs. }
            #                         ^1
        "};
        let results = complete_at_markers_with_context(src, TEST_CONTEXT_STUBS);
        let names = labels(&results[&1]);
        assert!(
            !names.contains(&"steam"),
            "no-module directive should suppress attrpath key completion, got: {names:?}"
        );
    }

    // ------------------------------------------------------------------
    // Completion items include doc comments from stubs
    // ------------------------------------------------------------------

    #[test]
    fn dot_completion_includes_docs() {
        // Dot completion on `config.` in a value position (Select expression).
        // Fields with `##` doc comments should have documentation set.
        let stubs = indoc! {"
            type TestConfig = {
                ## Enable the steam game launcher.
                steam: { enable: bool, ... },
                firefox: { enable: bool, ... },
                ...
            };
            val config :: TestConfig;
        "};
        let src = indoc! {"
            { config, ... }:
            let x = config.
            #              ^1
            in x
        "};
        let results = complete_at_markers_with_context(src, stubs);
        let items = &results[&1];
        let steam = items.iter().find(|i| i.label == "steam");
        assert!(
            steam.is_some(),
            "should complete steam, got: {:?}",
            labels(items)
        );
        assert_eq!(
            steam.unwrap().documentation,
            Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Enable the steam game launcher.".to_string()
            })),
            "steam should have doc comment from stubs"
        );
        // firefox has no doc comment — documentation should be None.
        let firefox = items.iter().find(|i| i.label == "firefox");
        assert!(firefox.is_some(), "should complete firefox");
        assert_eq!(
            firefox.unwrap().documentation,
            None,
            "firefox should have no documentation"
        );
    }

    #[test]
    fn attrpath_key_completion_includes_docs() {
        // Attrpath key completion on `programs.` — fields with `##` doc
        // comments should have documentation set on the CompletionItem.
        let stubs = indoc! {"
            type TestConfig = {
                programs: {
                    ## Enable the steam game launcher.
                    steam: { enable: bool, ... },
                    firefox: { enable: bool, ... },
                    ...
                },
                ...
            };
            val config :: TestConfig;
        "};
        let src = indoc! {"
            { config, ... }: { programs.
            #                           ^1
            }
        "};
        let results = complete_at_markers_with_context(src, stubs);
        let items = &results[&1];
        let steam = items.iter().find(|i| i.label == "steam");
        assert!(
            steam.is_some(),
            "should complete steam, got: {:?}",
            labels(items)
        );
        assert_eq!(
            steam.unwrap().documentation,
            Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Enable the steam game launcher.".to_string()
            })),
        );
        // firefox has no doc comment.
        let firefox = items.iter().find(|i| i.label == "firefox");
        assert!(firefox.is_some(), "should complete firefox");
        assert_eq!(firefox.unwrap().documentation, None);
    }

    // ==================================================================
    // NixOS config fixture integration tests
    // ==================================================================
    //
    // These tests exercise the full attrpath key completion pipeline with
    // realistic NixOS/Home Manager module structures: tix.toml context
    // config, .tix stubs with named types, glob-matched file paths, and
    // various Nix module patterns (plain return attrset, lib.mkIf wrapping,
    // nested attrsets, etc.).

    /// Minimal but realistic NixOS context stubs. Declares a `NixosConfig`
    /// type with nested `programs`, `services`, and `networking` sections,
    /// plus `Lib` with `mkIf`/`mkMerge` and `Pkgs`.
    const NIXOS_FIXTURE_STUBS: &str = indoc! {"
        type NixosConfig = {
            programs: {
                steam: {
                    enable: bool,
                    remotePlay: { enable: bool, ... },
                    ...
                },
                firefox: { enable: bool, ... },
                dconf: { enable: bool, ... },
                ...
            },
            services: {
                openssh: {
                    enable: bool,
                    settings: { PasswordAuthentication: bool, ... },
                    ...
                },
                pipewire: { enable: bool, ... },
                ...
            },
            networking: {
                firewall: { enable: bool, allowedTCPPorts: [int], ... },
                hostName: string,
                ...
            },
            ...
        };

        type Lib = { mkIf: bool -> a -> a, mkMerge: [a] -> a, ... };
        type Pkgs = { hello: string, firefox: string, ... };

        val config :: NixosConfig;
        val lib :: Lib;
        val pkgs :: Pkgs;
        val options :: { ... };
        val modulesPath :: path;
    "};

    /// Minimal Home Manager context stubs. Declares a `HomeManagerConfig`
    /// type with `programs` and `services` sections distinct from NixOS.
    const HM_FIXTURE_STUBS: &str = indoc! {"
        type HomeManagerConfig = {
            programs: {
                bash: { enable: bool, ... },
                git: { enable: bool, userName: string, ... },
                ...
            },
            services: {
                syncthing: { enable: bool, ... },
                ...
            },
            ...
        };

        type Lib = { mkIf: bool -> a -> a, ... };
        type Pkgs = { ... };

        val config :: HomeManagerConfig;
        val lib :: Lib;
        val pkgs :: Pkgs;
        val osConfig :: { ... };
    "};

    // ------------------------------------------------------------------
    // NixosFixtureProject: multi-file project with context stubs
    // ------------------------------------------------------------------

    /// A temporary project directory with tix.toml, .tix stubs, and .nix
    /// module files. Configures `AnalysisState` with project-level context
    /// so that attrpath key completion resolves through the stub types.
    struct NixosFixtureProject {
        temp_dir: std::path::PathBuf,
        state: AnalysisState,
    }

    fn next_fixture_id() -> u32 {
        use std::sync::atomic::{AtomicU32, Ordering};
        static FIXTURE_COUNTER: AtomicU32 = AtomicU32::new(0);
        FIXTURE_COUNTER.fetch_add(1, Ordering::Relaxed)
    }

    /// Create a fixture project with inline context stubs.
    ///
    /// Each context is a `(name, glob_patterns, stubs_content)` tuple.
    /// Stubs are written to `stubs/{name}.tix` and referenced from the
    /// project config.
    fn make_fixture(contexts: &[(&str, &[&str], &str)]) -> NixosFixtureProject {
        let id = next_fixture_id();
        let temp_dir =
            std::env::temp_dir().join(format!("tix_nixos_fixture_{}_{id}", std::process::id()));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let temp_dir = temp_dir.canonicalize().unwrap();

        let stubs_dir = temp_dir.join("stubs");
        std::fs::create_dir_all(&stubs_dir).unwrap();

        let mut context_map = std::collections::HashMap::new();
        for (name, globs, stubs_content) in contexts {
            let stub_filename = format!("{name}.tix");
            std::fs::write(stubs_dir.join(&stub_filename), stubs_content).unwrap();
            context_map.insert(
                name.to_string(),
                ContextConfig {
                    paths: globs.iter().map(|s| s.to_string()).collect(),
                    stubs: vec![format!("stubs/{stub_filename}")],
                },
            );
        }

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.project_config = Some(ProjectConfig {
            stubs: vec![],
            context: context_map,
            deadline: None,
            import_deadline: None,
        });
        state.config_dir = Some(temp_dir.clone());

        NixosFixtureProject { temp_dir, state }
    }

    /// Create a fixture project using `@builtin` context references.
    ///
    /// If `override_stubs` is provided, the registry's builtin stubs dir
    /// is set to a temp directory containing those files, so `@nixos` etc.
    /// resolve to the rich stubs instead of the compiled-in minimal ones.
    fn make_builtin_fixture(
        contexts: &[(&str, &[&str])],
        override_stubs: Option<&[(&str, &str)]>,
    ) -> NixosFixtureProject {
        let id = next_fixture_id();
        let temp_dir =
            std::env::temp_dir().join(format!("tix_builtin_fixture_{}_{id}", std::process::id()));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let temp_dir = temp_dir.canonicalize().unwrap();

        let mut registry = TypeAliasRegistry::default();
        if let Some(overrides) = override_stubs {
            let dir = temp_dir.join("builtin_override");
            std::fs::create_dir_all(&dir).unwrap();
            for (name, content) in overrides {
                std::fs::write(dir.join(format!("{name}.tix")), content).unwrap();
            }
            registry.set_builtin_stubs_dir(dir);
        }

        let mut context_map = std::collections::HashMap::new();
        for (name, globs) in contexts {
            context_map.insert(
                name.to_string(),
                ContextConfig {
                    paths: globs.iter().map(|s| s.to_string()).collect(),
                    stubs: vec![format!("@{name}")],
                },
            );
        }

        let mut state = AnalysisState::new(registry);
        state.project_config = Some(ProjectConfig {
            stubs: vec![],
            context: context_map,
            deadline: None,
            import_deadline: None,
        });
        state.config_dir = Some(temp_dir.clone());

        NixosFixtureProject { temp_dir, state }
    }

    impl NixosFixtureProject {
        /// Add (or update) a .nix module file at the given path relative to
        /// the project root. Parent directories are created automatically.
        fn add_file(&mut self, relative_path: &str, content: &str) {
            let path = self.temp_dir.join(relative_path);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(&path, content).unwrap();
            self.state.update_file(path, content.to_string());
        }

        /// Run completions at all `# ^N` marker positions in the file.
        fn complete_at_markers(&self, relative_path: &str) -> BTreeMap<u32, Vec<CompletionItem>> {
            let path = self.temp_dir.join(relative_path);
            let src = std::fs::read_to_string(&path).unwrap();
            let analysis = self.state.get_file(&path).expect("file not loaded").to_snapshot(0);
            let root = rnix::Root::parse(&src).tree();
            let markers = parse_markers(&src);
            let docs = &self.state.registry.docs;
            assert!(!markers.is_empty(), "no markers found in {relative_path}");

            markers
                .into_iter()
                .map(|(num, offset)| {
                    let pos = analysis.syntax.line_index.position(offset);
                    let items = match completion(&analysis, pos, &root, docs, &analysis.syntax.line_index) {
                        Some(CompletionResponse::Array(items)) => items,
                        _ => Vec::new(),
                    };
                    (num, items)
                })
                .collect()
        }
    }

    impl Drop for NixosFixtureProject {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.temp_dir);
        }
    }

    // ------------------------------------------------------------------
    // Integration tests: NixOS config completion with fixture stubs
    // ------------------------------------------------------------------

    #[test]
    fn nixos_fixture_programs_dot() {
        // The user's exact bug: `programs.` in a NixOS module should suggest
        // the program names from the config type.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam, got: {names:?}"
        );
        assert!(
            names.contains(&"firefox"),
            "should complete firefox, got: {names:?}"
        );
        assert!(
            names.contains(&"dconf"),
            "should complete dconf, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_nested_path() {
        // `programs.steam.` should suggest fields of the steam submodule.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, ... }: { programs.steam. }
                #                                 ^1
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"enable"),
            "should complete enable, got: {names:?}"
        );
        assert!(
            names.contains(&"remotePlay"),
            "should complete remotePlay, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_services_dot() {
        // `services.` should suggest service names.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, ... }: { services. }
                #                           ^1
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"openssh"),
            "should complete openssh, got: {names:?}"
        );
        assert!(
            names.contains(&"pipewire"),
            "should complete pipewire, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_deep_nesting() {
        // `services.openssh.settings.` should reach deeply nested fields.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, ... }: { services.openssh.settings. }
                #                                            ^1
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"PasswordAuthentication"),
            "should complete PasswordAuthentication, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_mkif_wrapping() {
        // NixOS modules commonly wrap the return attrset in `lib.mkIf`:
        //   { config, lib, ... }: { config = lib.mkIf cond { programs. }; }
        // Completion should still find the config type from the root lambda.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, lib, ... }:
                {
                  config = lib.mkIf true {
                    programs.
                #            ^1
                  };
                }
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam inside mkIf, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_mkif_config_guard() {
        // A common NixOS pattern: guard a config block with a config option
        // reference, e.g. `lib.mkIf config.programs.steam.enable { ... }`.
        // The `config.programs.steam.enable` is a Select on the config param,
        // and the attrset argument should still get attrpath key completion.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/gaming.nix",
            indoc! {"
                { config, lib, ... }:
                {
                  config = lib.mkIf config.programs.steam.enable {
                    networking.firewall.
                #                       ^1
                  };
                }
            "},
        );
        let results = project.complete_at_markers("modules/gaming.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"enable"),
            "should complete firewall.enable inside mkIf with config guard, got: {names:?}"
        );
        assert!(
            names.contains(&"allowedTCPPorts"),
            "should complete allowedTCPPorts inside mkIf with config guard, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_mkif_nested_config_guard() {
        // lib.mkIf guarded by a deeply nested config option reference.
        // The guard reads `config.services.pipewire.enable` and the body
        // configures a different section — a realistic cross-section pattern.
        let mut project = make_fixture(&[("nixos", &["**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "modules/audio.nix",
            indoc! {"
                { config, lib, ... }:
                lib.mkIf config.services.pipewire.enable {
                  services.openssh.
                #                  ^1
                }
            "},
        );
        let results = project.complete_at_markers("modules/audio.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"enable"),
            "should complete openssh.enable in mkIf with config guard, got: {names:?}"
        );
        assert!(
            names.contains(&"settings"),
            "should complete openssh.settings in mkIf with config guard, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_home_manager_context() {
        // Home Manager context should provide HM-specific completions,
        // not NixOS ones.
        let mut project = make_fixture(&[("home", &["**/*.nix"], HM_FIXTURE_STUBS)]);
        project.add_file(
            "modules/test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );
        let results = project.complete_at_markers("modules/test.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"bash"),
            "should complete bash, got: {names:?}"
        );
        assert!(
            names.contains(&"git"),
            "should complete git, got: {names:?}"
        );
        assert!(
            !names.contains(&"steam"),
            "should NOT complete steam in HM context, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_context_isolation() {
        // NixOS and HM files in the same project should get different
        // completions based on their context glob match.
        let mut project = make_fixture(&[
            ("nixos", &["hosts/**/*.nix"], NIXOS_FIXTURE_STUBS),
            ("home", &["home/**/*.nix"], HM_FIXTURE_STUBS),
        ]);
        project.add_file(
            "hosts/test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );
        project.add_file(
            "home/test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );

        // NixOS file should get NixOS completions.
        let nixos_results = project.complete_at_markers("hosts/test.nix");
        let nixos_names = labels(&nixos_results[&1]);
        assert!(
            nixos_names.contains(&"steam"),
            "NixOS file should complete steam, got: {nixos_names:?}"
        );

        // HM file should get HM completions.
        let hm_results = project.complete_at_markers("home/test.nix");
        let hm_names = labels(&hm_results[&1]);
        assert!(
            hm_names.contains(&"bash"),
            "HM file should complete bash, got: {hm_names:?}"
        );
        assert!(
            !hm_names.contains(&"steam"),
            "HM file should NOT complete steam, got: {hm_names:?}"
        );
    }

    #[test]
    fn nixos_fixture_hosts_glob() {
        // Deeply nested file paths should match `hosts/**/*.nix` glob.
        let mut project = make_fixture(&[("nixos", &["hosts/**/*.nix"], NIXOS_FIXTURE_STUBS)]);
        project.add_file(
            "hosts/desktop/gaming.nix",
            indoc! {"
                { pkgs, config, ... }: { programs. }
                #                                 ^1
            "},
        );
        let results = project.complete_at_markers("hosts/desktop/gaming.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "should complete steam via hosts glob, got: {names:?}"
        );
    }

    #[test]
    fn nixos_fixture_builtin_stubs_have_completions() {
        // The compiled-in @nixos stubs (generated at depth 4) now include
        // full option trees. Using @nixos without any override dir should
        // produce completions for top-level option groups.
        let mut project = make_builtin_fixture(&[("nixos", &["**/*.nix"])], None);
        project.add_file(
            "test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );
        let results = project.complete_at_markers("test.nix");
        let names = labels(&results[&1]);
        assert!(
            !names.is_empty(),
            "builtin @nixos stubs should produce completions, got: {names:?}"
        );
    }

    #[test]
    fn builtin_override_stubs_surface_docs_in_completion() {
        // When TIX_BUILTIN_STUBS overrides the compiled-in stubs with richer
        // stubs that include `##` doc comments, the DocIndex gets populated
        // and completion items carry the documentation field.
        let rich_stubs = indoc! {"
            type NixosConfig = {
                programs: {
                    ## Whether to enable the steam game platform.
                    steam: { enable: bool, ... },
                    firefox: { enable: bool, ... },
                    ...
                },
                ...
            };
            val config :: NixosConfig;
            val lib :: { ... };
            val pkgs :: { ... };
        "};
        let mut project =
            make_builtin_fixture(&[("nixos", &["**/*.nix"])], Some(&[("nixos", rich_stubs)]));
        project.add_file(
            "test.nix",
            indoc! {"
                { config, ... }: { programs. }
                #                           ^1
            "},
        );
        let results = project.complete_at_markers("test.nix");
        let items = &results[&1];
        let steam = items.iter().find(|i| i.label == "steam");
        assert!(
            steam.is_some(),
            "should complete steam, got: {:?}",
            labels(items)
        );
        assert_eq!(
            steam.unwrap().documentation,
            Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Whether to enable the steam game platform.".to_string()
            })),
            "steam completion item should carry doc from override stubs"
        );
        // firefox has no doc comment — should be None.
        let firefox = items.iter().find(|i| i.label == "firefox");
        assert!(firefox.is_some(), "should complete firefox");
        assert_eq!(firefox.unwrap().documentation, None);
    }

    #[test]
    fn generated_stubs_surface_docs_in_completion() {
        // End-to-end: load the real generated stubs from stubs/generated/
        // (produced by `just gen-stubs`) as an override, and verify that
        // doc comments appear on completion items.
        let generated_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../stubs/generated")
            .canonicalize();
        let generated_dir = match generated_dir {
            Ok(dir) if dir.join("nixos.tix").is_file() => dir,
            _ => {
                // Generated stubs don't exist (CI or fresh clone without
                // `just gen-stubs`). Skip rather than fail.
                eprintln!("skipping: stubs/generated/nixos.tix not found (run `just gen-stubs`)");
                return;
            }
        };
        let mut registry = TypeAliasRegistry::default();
        registry.set_builtin_stubs_dir(generated_dir);

        let mut context_map = std::collections::HashMap::new();
        context_map.insert(
            "nixos".to_string(),
            ContextConfig {
                paths: vec!["**/*.nix".to_string()],
                stubs: vec!["@nixos".to_string()],
            },
        );
        let temp_dir = std::env::temp_dir().join(format!(
            "tix_gen_stubs_doc_test_{}_{}",
            std::process::id(),
            next_fixture_id(),
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let temp_dir = temp_dir.canonicalize().unwrap();

        let mut state = AnalysisState::new(registry);
        state.project_config = Some(ProjectConfig {
            stubs: vec![],
            context: context_map,
            deadline: None,
            import_deadline: None,
        });
        state.config_dir = Some(temp_dir.clone());

        let src = indoc! {"
            { config, ... }: { programs. }
            #                           ^1
        "};
        let nix_path = temp_dir.join("test.nix");
        std::fs::write(&nix_path, src).unwrap();
        state.update_file(nix_path.clone(), src.to_string());

        let analysis = state.get_file(&nix_path).unwrap().to_snapshot(0);
        let root = rnix::Root::parse(src).tree();
        let docs = &state.registry.docs;
        let markers = parse_markers(src);
        let pos = analysis.syntax.line_index.position(markers[&1]);
        let items = match completion(&analysis, pos, &root, docs, &analysis.syntax.line_index) {
            Some(CompletionResponse::Array(items)) => items,
            _ => Vec::new(),
        };

        // The generated stubs should produce completions.
        assert!(
            !items.is_empty(),
            "generated stubs should produce completions"
        );

        // At least some fields under `programs` should have doc comments.
        let with_docs: Vec<_> = items
            .iter()
            .filter(|i| i.documentation.is_some())
            .map(|i| i.label.as_str())
            .collect();
        assert!(
            !with_docs.is_empty(),
            "expected some completion items with docs from generated stubs, but none had documentation. \
             First 5 items: {:?}",
            items.iter().take(5).map(|i| (&i.label, &i.documentation)).collect::<Vec<_>>()
        );

        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    // ======================================================================
    // On-disk fixture tests (test/nixos_fixture/)
    // ======================================================================
    //
    // These load real Nix files from test/nixos_fixture/ and verify
    // completion through the full pipeline: tix.toml discovery -> stub
    // loading -> context injection -> completion.

    /// Set up an AnalysisState pointing at the test/nixos_fixture/ directory.
    ///
    /// Loads the fixture's tix.toml and configures the state so that
    /// context resolution works for files under the fixture directory.
    /// Uses `with_builtins()` so that Lib/Pkgs from `stubs/lib.tix` resolve
    /// when context stubs reference them.
    fn fixture_state() -> (AnalysisState, PathBuf) {
        let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../test/nixos_fixture")
            .canonicalize()
            .expect("test/nixos_fixture fixture directory must exist");

        let config_path = fixture_dir.join("tix.toml");
        let config = crate::project_config::load_config(&config_path)
            .expect("fixture tix.toml should parse");

        let mut state = AnalysisState::new(TypeAliasRegistry::with_builtins());
        state.project_config = Some(config);
        state.config_dir = Some(fixture_dir.clone());

        (state, fixture_dir)
    }

    /// Run completions at marker positions in a fixture file.
    fn complete_fixture_markers(rel_path: &str) -> BTreeMap<u32, Vec<CompletionItem>> {
        let (mut state, fixture_dir) = fixture_state();
        let file_path = fixture_dir.join(rel_path);
        let src = std::fs::read_to_string(&file_path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file_path.display()));

        let markers = parse_markers(&src);
        assert!(!markers.is_empty(), "no markers in {rel_path}");

        state.update_file(file_path.clone(), src.clone());
        let analysis = state.get_file(&file_path).unwrap().to_snapshot(0);
        let root = rnix::Root::parse(&src).tree();
        let docs = &state.registry.docs;

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = analysis.syntax.line_index.position(offset);
                let items = match completion(&analysis, pos, &root, docs, &analysis.syntax.line_index) {
                    Some(CompletionResponse::Array(items)) => items,
                    _ => Vec::new(),
                };
                (num, items)
            })
            .collect()
    }

    #[test]
    fn fixture_gaming_nix_programs() {
        // gaming.nix has `programs.` with a marker — should complete with
        // steam, firefox, etc. from the fixture's nixos.tix stubs.
        let results = complete_fixture_markers("hosts/desktop/gaming.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"steam"),
            "expected steam in gaming.nix, got: {names:?}"
        );
        assert!(
            names.contains(&"firefox"),
            "expected firefox in gaming.nix, got: {names:?}"
        );
    }

    #[test]
    fn fixture_home_shell_nix_programs() {
        // home/shell.nix uses the @home-manager context (via tix.toml
        // `[context.home]`). The compiled-in HM stubs define
        // HomeManagerConfig with programs, services, etc. Verify that
        // `programs.` completion includes common HM program modules.
        let results = complete_fixture_markers("home/shell.nix");
        let names = labels(&results[&1]);
        assert!(
            names.contains(&"fish"),
            "expected fish in home/shell.nix programs completion, got: {names:?}"
        );
        assert!(
            names.contains(&"git"),
            "expected git in home/shell.nix programs completion, got: {names:?}"
        );
        assert!(
            names.contains(&"bash"),
            "expected bash in home/shell.nix programs completion, got: {names:?}"
        );
    }
}
