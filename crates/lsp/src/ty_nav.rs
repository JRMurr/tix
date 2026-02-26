// ==============================================================================
// Type navigation helpers
// ==============================================================================
//
// General-purpose utilities for traversing and querying OutputTy structures.
// Used by both completion and hover to resolve attrset fields, walk through
// type aliases, and extract lambda parameter types.

use std::collections::{BTreeMap, HashMap};

use comment_parser::{ParsedTy, TypeVarValue};
use lang_ast::Expr;
use lang_check::aliases::TypeAliasRegistry;
use lang_ty::{AttrSetTy, OutputTy, TyRef};
use rowan::ast::AstNode;
use smol_str::SmolStr;

use crate::state::FileSnapshot;

/// Extract a plain string literal from an rnix Str node (no interpolation).
pub(crate) fn get_str_literal(s: &rnix::ast::Str) -> Option<SmolStr> {
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
pub(crate) fn resolve_through_segments(ty: &OutputTy, segments: &[SmolStr]) -> Option<OutputTy> {
    let mut current = ty.clone();
    for seg in segments {
        let fields = collect_attrset_fields(&current);
        let field_ty = fields.get(seg)?;
        current = (*field_ty.0).clone();
    }
    Some(current)
}

/// Find the module config type (e.g. NixosConfig) from the root lambda's
/// pattern fields, based on the first attrpath segment.
///
/// First checks explicitly destructured pattern fields (e.g. `config` in
/// `{ config, ... }:`). If no match is found and the pattern has `...`,
/// falls back to checking `context_arg_types` — these are the resolved types
/// from tix.toml context args that weren't explicitly named in the pattern
/// (e.g. `config :: NixosConfig` when the module only writes `{ pkgs, ... }:`).
///
/// Also handles plain attrset modules (no lambda wrapper at all) by checking
/// context_arg_types directly — NixOS modules can be `{ services.foo = ...; }`
/// without any function.
///
/// Returns `None` when no pattern field or context arg type contains the
/// given segment.
pub(crate) fn get_module_config_type(
    analysis: &FileSnapshot,
    inference: &lang_check::InferenceResult,
    first_segment: &SmolStr,
    context_arg_types: &HashMap<SmolStr, OutputTy>,
) -> Option<OutputTy> {
    // Escape hatch: a `/** no-module */` comment at the top of the file
    // opts out of all module-aware hover/completion. Useful for files that
    // match a tix.toml glob but aren't actually NixOS/HM modules.
    if has_no_module_directive(analysis) {
        return None;
    }

    let root_expr_id = analysis.syntax.module.entry_expr;

    match &analysis.syntax.module[root_expr_id] {
        // Pattern lambda: check destructured fields first, then fall through
        // to context_arg_types if the pattern has `...`.
        Expr::Lambda { pat: Some(pat), .. } => {
            for (name_id, _default) in pat.fields.iter() {
                let Some(name_id) = name_id else { continue };
                if let Some(ty) = inference.name_ty_map.get(*name_id) {
                    let fields = collect_attrset_fields(ty);
                    if fields.contains_key(first_segment) {
                        return Some(ty.clone());
                    }
                }
            }

            // Only fall through to context_arg_types if the pattern has `...`
            // (i.e. it accepts extra args beyond those listed).
            if !pat.ellipsis {
                return None;
            }
        }

        // Plain lambda (no pattern, e.g. `config: body`) is not a NixOS module
        // convention — don't use context_arg_types.
        Expr::Lambda { pat: None, .. } => return None,

        // Non-lambda root (plain attrset, etc.): fall through to
        // context_arg_types. NixOS modules can be plain `{ services.foo = ...; }`.
        _ => {}
    }

    // Fallback: check context arg types. Covers two cases:
    // 1. Lambda with `...` where `config` isn't destructured
    //    (e.g. `{ pkgs, ... }:`)
    // 2. Plain attrset module with no lambda wrapper
    //    (e.g. `{ services.openssh.enable = true; }`)
    for ty in context_arg_types.values() {
        let fields = collect_attrset_fields(ty);
        if fields.contains_key(first_segment) {
            return Some(ty.clone());
        }
    }

    None
}

/// Check whether the file has a `no-module` directive in its leading comments.
///
/// Scans the first tokens of the syntax tree for a comment containing
/// `no-module`. Both line comments (`# no-module`) and block comments
/// (`/** no-module */`) are recognized. Stops at the first non-trivia token
/// (i.e. the first real code token).
fn has_no_module_directive(analysis: &FileSnapshot) -> bool {
    use rnix::SyntaxKind;

    let root = analysis.syntax.parsed.tree();
    for token in root.syntax().descendants_with_tokens() {
        let rowan::NodeOrToken::Token(t) = token else {
            continue;
        };
        match t.kind() {
            SyntaxKind::TOKEN_COMMENT => {
                if t.text().contains("no-module") {
                    return true;
                }
            }
            SyntaxKind::TOKEN_WHITESPACE => continue,
            // Stop at the first non-trivia token.
            _ => break,
        }
    }
    false
}

/// Walk up through nested AttrSet → AttrpathValue chains to collect parent
/// path context.
///
/// For `{ services.openssh = { enable. } }`, when called on the inner AttrSet
/// (the one containing `enable.`), this returns `["services", "openssh"]` —
/// the segments from the outer AttrpathValue that nests into this AttrSet.
pub(crate) fn collect_parent_attrpath_context(attrset_node: &rnix::ast::AttrSet) -> Vec<SmolStr> {
    let mut all_segments = Vec::new();
    let mut current = attrset_node.syntax().clone();

    loop {
        // Check if this AttrSet is the value of an AttrpathValue.
        let Some(parent) = current.parent() else {
            break;
        };
        let Some(apv) = rnix::ast::AttrpathValue::cast(parent) else {
            break;
        };

        // Collect all segments from the parent AttrpathValue's attrpath.
        if let Some(attrpath) = apv.attrpath() {
            let mut parent_segs = Vec::new();
            for attr in attrpath.attrs() {
                let name = match attr {
                    rnix::ast::Attr::Ident(ref ident) => {
                        ident.ident_token().map(|t| SmolStr::from(t.text()))
                    }
                    rnix::ast::Attr::Str(ref s) => get_str_literal(s),
                    rnix::ast::Attr::Dynamic(_) => None,
                };
                match name {
                    Some(n) if !n.is_empty() => parent_segs.push(n),
                    _ => break,
                }
            }
            // Prepend parent segments (outer-to-inner order).
            all_segments.splice(0..0, parent_segs);
        }

        // Move up to the AttrSet that contains this AttrpathValue.
        let Some(grandparent) = apv.syntax().parent() else {
            break;
        };
        if !rnix::ast::AttrSet::can_cast(grandparent.kind()) {
            break;
        }
        current = grandparent;
    }

    all_segments
}

/// Extract attrset fields from a type, unwrapping Named, Intersection, and Union
/// wrappers as appropriate.
pub(crate) fn collect_attrset_fields(ty: &OutputTy) -> BTreeMap<SmolStr, TyRef> {
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
pub(crate) fn extract_lambda_param(ty: &OutputTy) -> Option<OutputTy> {
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
        // For a union of lambdas (e.g. canonicalization produced
        // `(A→B) | (A→C)`), extract the param from the first lambda member.
        // The param types are typically identical across union members.
        OutputTy::Union(members) => {
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

/// Extract the type alias name from an OutputTy, if it's a Named type.
pub(crate) fn extract_alias_name(ty: &OutputTy) -> Option<&SmolStr> {
    match ty {
        OutputTy::Named(name, _) => Some(name),
        _ => None,
    }
}

/// Convert a `ParsedTy` (from .tix stub files) to an `OutputTy`, resolving alias
/// references through the `TypeAliasRegistry`.
///
/// This is needed because context args are stored as `ParsedTy` but the LSP
/// works with `OutputTy` for field lookups and hover display.
pub(crate) fn parsed_ty_to_output_ty(
    ty: &ParsedTy,
    registry: &TypeAliasRegistry,
    depth: usize,
) -> OutputTy {
    // Prevent infinite recursion on self-referential aliases.
    if depth > 20 {
        return OutputTy::TyVar(0);
    }

    match ty {
        // comment_parser uses lang_ty::PrimitiveTy directly, so clone is safe.
        ParsedTy::Primitive(p) => OutputTy::Primitive(*p),

        ParsedTy::TyVar(TypeVarValue::Reference(name)) => {
            // Look up alias in registry and wrap in Named.
            if let Some(alias_body) = registry.get(name) {
                let inner = parsed_ty_to_output_ty(alias_body, registry, depth + 1);
                OutputTy::Named(name.clone(), TyRef::from(inner))
            } else {
                // Unresolved reference — treat as opaque type variable.
                OutputTy::TyVar(0)
            }
        }

        ParsedTy::TyVar(TypeVarValue::Generic(_)) => {
            // Generics don't matter for field lookup — placeholder.
            OutputTy::TyVar(0)
        }

        ParsedTy::List(inner) => OutputTy::List(TyRef::from(parsed_ty_to_output_ty(
            &inner.0,
            registry,
            depth + 1,
        ))),

        ParsedTy::Lambda { param, body } => OutputTy::Lambda {
            param: TyRef::from(parsed_ty_to_output_ty(&param.0, registry, depth + 1)),
            body: TyRef::from(parsed_ty_to_output_ty(&body.0, registry, depth + 1)),
        },

        ParsedTy::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(name, ty_ref)| {
                    (
                        name.clone(),
                        TyRef::from(parsed_ty_to_output_ty(&ty_ref.0, registry, depth + 1)),
                    )
                })
                .collect();
            let dyn_ty = attr
                .dyn_ty
                .as_ref()
                .map(|d| TyRef::from(parsed_ty_to_output_ty(&d.0, registry, depth + 1)));
            OutputTy::AttrSet(AttrSetTy {
                fields,
                dyn_ty,
                open: attr.open,
                optional_fields: attr.optional_fields.clone(),
            })
        }

        ParsedTy::Union(members) => OutputTy::Union(
            members
                .iter()
                .map(|m| TyRef::from(parsed_ty_to_output_ty(&m.0, registry, depth + 1)))
                .collect(),
        ),

        ParsedTy::Intersection(members) => OutputTy::Intersection(
            members
                .iter()
                .map(|m| TyRef::from(parsed_ty_to_output_ty(&m.0, registry, depth + 1)))
                .collect(),
        ),
    }
}

/// Collect attrpath segments from an Attrpath node, relative to a boundary position.
///
/// When `inclusive` is true (hover), includes the segment whose end >= boundary.
/// When `inclusive` is false (completion), excludes segments whose start >= boundary.
/// Handles both Ident and Str attrs.
pub(crate) fn collect_attrpath_segments(
    attrpath: &rnix::ast::Attrpath,
    boundary: rowan::TextSize,
    inclusive: bool,
) -> Vec<SmolStr> {
    let mut segments = Vec::new();

    for attr in attrpath.attrs() {
        // In exclusive mode (completion), skip segments at or after the boundary.
        if !inclusive && attr.syntax().text_range().start() >= boundary {
            break;
        }

        let name = match attr {
            rnix::ast::Attr::Ident(ref ident) => {
                ident.ident_token().map(|t| SmolStr::from(t.text()))
            }
            rnix::ast::Attr::Str(ref s) => get_str_literal(s),
            rnix::ast::Attr::Dynamic(_) => None,
        };

        match name {
            Some(n) if !n.is_empty() => {
                segments.push(n);
                // In inclusive mode (hover), stop after the boundary segment.
                if inclusive && attr.syntax().text_range().end() >= boundary {
                    break;
                }
            }
            _ => break,
        }
    }

    segments
}
