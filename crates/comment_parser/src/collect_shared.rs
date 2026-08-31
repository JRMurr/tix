// ==============================================================================
// Shared type-collection helpers
// ==============================================================================
//
// Pure functions used by both `collect.rs` (doc comment parser) and
// `tix_collect.rs` (.tix file parser). These don't depend on pest's
// grammar-specific `Rule` enums, so they can be shared without macros.

use smol_str::SmolStr;

use crate::{CollectError, FieldDoc, FieldSource, ParsedTy, ParsedTyRef, SourceLocation};

/// Strip surrounding double quotes from a string literal.
pub fn unquote_string_literal(s: &str) -> String {
    s.trim_matches('"').to_string()
}

/// Parse a source location string like `nixpkgs:lib/trivial.nix:61:8`.
/// Splits from the right on `:` to extract line/column, then splits the
/// remaining prefix on the first `:` to separate source_id from relative_path.
pub(crate) fn parse_source_loc(s: &str) -> Option<SourceLocation> {
    // Split from right: last segment is column, second-to-last is line.
    let last_colon = s.rfind(':')?;
    let column: u32 = s[last_colon + 1..].parse().ok()?;
    let rest = &s[..last_colon];
    let second_colon = rest.rfind(':')?;
    let line: u32 = rest[second_colon + 1..].parse().ok()?;
    let id_and_path = &rest[..second_colon];

    // Split source_id from relative_path on the first `:`.
    let (source_id, relative_path) = id_and_path.split_once(':')?;
    if source_id.is_empty() || relative_path.is_empty() {
        return None;
    }
    Some(SourceLocation {
        source_id: SmolStr::from(source_id),
        relative_path: SmolStr::from(relative_path),
        line,
        column,
    })
}

/// Mutable state threaded through type-expression collection: field-level doc
/// comments and `@source` annotations are parsed inside attrsets but need to
/// be reported at the file level, with their full nesting path.
pub(crate) struct CollectCtx {
    pub(crate) field_docs: Vec<FieldDoc>,
    pub(crate) field_sources: Vec<FieldSource>,
    /// Current nesting path within a type alias body (e.g. `["NixosConfig", "services"]`).
    field_path: Vec<SmolStr>,
}

impl CollectCtx {
    pub(crate) fn new() -> Self {
        Self {
            field_docs: Vec::new(),
            field_sources: Vec::new(),
            field_path: Vec::new(),
        }
    }

    pub(crate) fn push_field_doc(&mut self, field_name: SmolStr, doc: SmolStr) {
        let mut full_path = self.field_path.clone();
        full_path.push(field_name);
        self.field_docs.push(FieldDoc {
            path: full_path,
            doc,
        });
    }

    pub(crate) fn push_field_source(&mut self, field_name: SmolStr, source: SourceLocation) {
        let mut full_path = self.field_path.clone();
        full_path.push(field_name);
        self.field_sources.push(FieldSource {
            path: full_path,
            source,
        });
    }

    pub(crate) fn set_path(&mut self, path: Vec<SmolStr>) {
        self.field_path = path;
    }

    pub(crate) fn path(&self) -> &[SmolStr] {
        &self.field_path
    }
}

/// Normalize a collected member list into a single type:
/// - 0 members → error with `kind_name`
/// - 1 member → unwrap to avoid a spurious wrapper
/// - 2+ members → call `wrap` to produce Union or Intersection
pub fn normalize_set_type(
    mut members: Vec<ParsedTyRef>,
    kind_name: &str,
    wrap: fn(Vec<ParsedTyRef>) -> ParsedTy,
) -> Result<ParsedTy, CollectError> {
    match members.len() {
        0 => Err(CollectError::new(format!(
            "{kind_name} type must have at least one member",
        ))),
        1 => {
            let single = members.pop().expect("len checked above");
            Ok((*single.0).clone())
        }
        _ => Ok(wrap(members)),
    }
}
