// ==============================================================================
// Shared type-collection helpers
// ==============================================================================
//
// Pure functions used by both `collect.rs` (doc comment parser) and
// `tix_collect.rs` (.tix file parser). These don't depend on pest's
// grammar-specific `Rule` enums, so they can be shared without macros.

use crate::{CollectError, ParsedTy, ParsedTyRef};

/// Strip surrounding double quotes from a string literal.
pub fn unquote_string_literal(s: &str) -> String {
    s.trim_matches('"').to_string()
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
