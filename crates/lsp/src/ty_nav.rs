// ==============================================================================
// Type navigation helpers
// ==============================================================================
//
// General-purpose utilities for traversing and querying OutputTy structures.
// Used by both completion and hover to resolve attrset fields, walk through
// type aliases, and extract lambda parameter types.

use std::collections::BTreeMap;

use lang_ast::Expr;
use lang_ty::{OutputTy, TyRef};
use rowan::ast::AstNode;
use smol_str::SmolStr;

use crate::state::FileAnalysis;

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
/// Returns `None` when:
/// - The root expression isn't a lambda with pattern params
/// - No pattern field's type contains the given segment (e.g. not a NixOS module,
///   or context stubs aren't loaded)
pub(crate) fn get_module_config_type(
    analysis: &FileAnalysis,
    inference: &lang_check::InferenceResult,
    first_segment: &SmolStr,
) -> Option<OutputTy> {
    let root_expr_id = analysis.module.entry_expr;

    let Expr::Lambda { pat: Some(pat), .. } = &analysis.module[root_expr_id] else {
        return None;
    };

    // Search each pattern field for a type that has the first segment.
    for (name_id, _default) in pat.fields.iter() {
        let Some(name_id) = name_id else { continue };
        if let Some(ty) = inference.name_ty_map.get(*name_id) {
            let fields = collect_attrset_fields(ty);
            if fields.contains_key(first_segment) {
                return Some(ty.clone());
            }
        }
    }

    None
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
