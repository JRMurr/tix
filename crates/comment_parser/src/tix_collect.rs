// ==============================================================================
// .tix declaration file collection
// ==============================================================================
//
// Walks the pest parse tree from `tix_decl.pest` and produces structured
// `TixDeclFile` / `TixDeclaration` values. Type expression collection mirrors
// `collect.rs` but uses `tix_parser::Rule` variants.
//
// COUPLING NOTICE: The type expression collection functions below
// (collect_type_expr, collect_one, collect_union, collect_intersection,
// collect_attrset) are structurally duplicated from `collect.rs`.
// See the coupling notice in that file for the rationale. When modifying
// shared type expression logic, update both files together.

use lang_ty::{AttrSetTy, PrimitiveTy};
use pest::iterators::{Pair, Pairs};
use smol_str::SmolStr;
use std::collections::BTreeMap;

use crate::tix_parser::Rule;
use crate::{
    CollectError, FieldDoc, ParsedTy, ParsedTyRef, SourceLocation, TixDeclFile, TixDeclaration,
    TypeVarValue,
};

// =============================================================================
// Doc block extraction
// =============================================================================
//
// A `doc_block` contains one or more `doc_comment` children. Each `doc_comment`
// matches `"##" ~ (!"\n" ~ ANY)*`. We strip the leading `## ` (or bare `##`)
// prefix and join multiple lines with newlines.

fn extract_doc_block(pair: &Pair<Rule>) -> SmolStr {
    debug_assert_eq!(pair.as_rule(), Rule::doc_block);
    let lines: Vec<&str> = pair
        .clone()
        .into_inner()
        .map(|comment| {
            let text = comment.as_str();
            // Strip the `##` prefix.
            let rest = &text[2..];
            // Strip a single leading space if present (conventional `## text`).
            rest.strip_prefix(' ').unwrap_or(rest)
        })
        .collect();
    SmolStr::from(lines.join("\n"))
}

/// Try to extract a doc_block from the first child of `inner` if it matches.
/// Returns `(Option<SmolStr>, Pairs)` -- the doc (if present) and the remaining
/// children with the doc_block consumed.
fn take_doc_block(inner: &mut Pairs<Rule>) -> Option<SmolStr> {
    let first = inner.peek()?;
    if first.as_rule() == Rule::doc_block {
        let doc = extract_doc_block(&first);
        inner.next(); // consume it
        Some(doc)
    } else {
        None
    }
}

// =============================================================================
// Source annotation extraction
// =============================================================================

/// Try to extract a `source_annotation` from the next child of `inner`.
/// Returns `Option<SourceLocation>` and consumes the pair if matched.
fn take_source_annotation(inner: &mut Pairs<Rule>) -> Option<SourceLocation> {
    let first = inner.peek()?;
    if first.as_rule() == Rule::source_annotation {
        inner.next(); // consume the source_annotation pair
        let source_loc = first.into_inner().next()?; // the source_loc child
        parse_source_loc(source_loc.as_str().trim())
    } else {
        None
    }
}

/// Parse a source location string like `nixpkgs:lib/trivial.nix:61:8`.
/// Splits from the right on `:` to handle paths that may contain colons.
fn parse_source_loc(s: &str) -> Option<SourceLocation> {
    // Split from right: last segment is column, second-to-last is line,
    // everything before is the source-id-prefixed path.
    let last_colon = s.rfind(':')?;
    let column: u32 = s[last_colon + 1..].parse().ok()?;
    let rest = &s[..last_colon];
    let second_colon = rest.rfind(':')?;
    let line: u32 = rest[second_colon + 1..].parse().ok()?;
    let path = &rest[..second_colon];
    if path.is_empty() {
        return None;
    }
    Some(SourceLocation {
        path: SmolStr::from(path),
        line,
        column,
    })
}

/// Helper to build a CollectError with span information from a pest Pair.
fn err_at_pair(message: impl Into<String>, pair: &Pair<Rule>) -> CollectError {
    let span = pair.as_span();
    CollectError::with_span(message, span.start(), span.end())
}

// =============================================================================
// Top-level collection
// =============================================================================

pub fn collect_tix_file(pairs: Pairs<Rule>) -> Result<TixDeclFile, CollectError> {
    let mut declarations = Vec::new();
    let mut ctx = CollectCtx::new();

    collect_tix_file_inner(pairs, &mut declarations, &mut ctx)?;

    Ok(TixDeclFile {
        declarations,
        field_docs: ctx.field_docs,
    })
}

fn collect_tix_file_inner(
    pairs: Pairs<Rule>,
    declarations: &mut Vec<TixDeclaration>,
    ctx: &mut CollectCtx,
) -> Result<(), CollectError> {
    for pair in pairs {
        match pair.as_rule() {
            Rule::tix_file => {
                collect_tix_file_inner(pair.into_inner(), declarations, ctx)?;
                return Ok(());
            }
            Rule::type_alias_decl => {
                let pair_span = pair.as_span();
                let span = (pair_span.start(), pair_span.end());
                let mut inner = pair.into_inner();
                let doc = take_doc_block(&mut inner);
                let source = take_source_annotation(&mut inner);
                let name: SmolStr = inner
                    .next()
                    .ok_or_else(|| CollectError::new("type_alias_decl missing identifier"))?
                    .as_str()
                    .into();

                // Set path context so field-level doc comments in the body
                // get the correct prefix (e.g. ["Config", "services", "enable"]).
                ctx.set_path(vec![name.clone()]);
                let body = collect_type_expr(inner, ctx)?.ok_or_else(|| {
                    CollectError::new(format!("type alias '{name}' has empty body"))
                })?;
                ctx.set_path(Vec::new());

                declarations.push(TixDeclaration::TypeAlias {
                    name,
                    body,
                    doc,
                    span,
                    source,
                });
            }
            Rule::val_decl => {
                let pair_span = pair.as_span();
                let span = (pair_span.start(), pair_span.end());
                let mut inner = pair.into_inner();
                let doc = take_doc_block(&mut inner);
                let source = take_source_annotation(&mut inner);
                let name: SmolStr = inner
                    .next()
                    .ok_or_else(|| CollectError::new("val_decl missing identifier"))?
                    .as_str()
                    .into();
                let ty = collect_type_expr(inner, ctx)?.ok_or_else(|| {
                    CollectError::new(format!("val declaration '{name}' has empty type"))
                })?;
                declarations.push(TixDeclaration::ValDecl {
                    name,
                    ty,
                    doc,
                    span,
                    source,
                });
            }
            Rule::module_decl => {
                let pair_span = pair.as_span();
                let span = (pair_span.start(), pair_span.end());
                let mut inner = pair.into_inner();
                let doc = take_doc_block(&mut inner);
                let source = take_source_annotation(&mut inner);
                let name: SmolStr = inner
                    .next()
                    .ok_or_else(|| CollectError::new("module_decl missing identifier"))?
                    .as_str()
                    .into();
                // Remaining children are the nested declarations.
                let mut nested = Vec::new();
                collect_tix_file_inner(inner, &mut nested, ctx)?;
                declarations.push(TixDeclaration::Module {
                    name,
                    declarations: nested,
                    doc,
                    span,
                    source,
                });
            }
            Rule::EOI => {}
            _ => {
                return Err(err_at_pair(
                    format!(
                        "unexpected rule {:?} at top level of .tix file",
                        pair.as_rule()
                    ),
                    &pair,
                ));
            }
        }
    }
    Ok(())
}

// =============================================================================
// Collection context
// =============================================================================
//
// Field-level doc comments are parsed inside attrsets but need to be reported
// at the TixDeclFile level. `CollectCtx` carries this mutable state explicitly
// through the recursive collection functions, avoiding hidden thread-local state.

struct CollectCtx {
    field_docs: Vec<FieldDoc>,
    field_doc_path: Vec<SmolStr>,
}

impl CollectCtx {
    fn new() -> Self {
        Self {
            field_docs: Vec::new(),
            field_doc_path: Vec::new(),
        }
    }

    fn push_field_doc(&mut self, field_name: SmolStr, doc: SmolStr) {
        let mut full_path = self.field_doc_path.clone();
        full_path.push(field_name);
        self.field_docs.push(FieldDoc {
            path: full_path,
            doc,
        });
    }

    fn set_path(&mut self, path: Vec<SmolStr>) {
        self.field_doc_path = path;
    }

    fn path(&self) -> &[SmolStr] {
        &self.field_doc_path
    }
}

// =============================================================================
// Type expression collection -- mirrors collect.rs but for tix_parser::Rule
// =============================================================================

fn collect_type_expr(
    mut pairs: Pairs<Rule>,
    ctx: &mut CollectCtx,
) -> Result<Option<ParsedTy>, CollectError> {
    let curr = match pairs.next() {
        Some(c) => c,
        None => return Ok(None),
    };

    let curr = match curr.as_rule() {
        // Transparent wrappers.
        Rule::type_expr
        | Rule::arrow_segment
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref
        | Rule::atom_type => collect_type_expr(curr.into_inner(), ctx)?.ok_or_else(|| {
            CollectError::new("expected type expression inside wrapper, found empty")
        })?,

        Rule::union_type => collect_union(curr.into_inner(), ctx)?,
        Rule::isect_type => collect_intersection(curr.into_inner(), ctx)?,
        Rule::postfix_type => collect_postfix(curr.into_inner(), ctx)?,
        Rule::typeof_expr => collect_typeof(curr.into_inner())?,
        Rule::import_type => collect_import_type(curr.into_inner())?,
        Rule::applied_type => collect_applied_type(curr.into_inner(), ctx)?,

        Rule::attrset_type => collect_attrset(curr.into_inner(), ctx)?,
        Rule::list_type => {
            let inner = collect_type_expr(curr.into_inner(), ctx)?
                .ok_or_else(|| CollectError::new("list type has empty element type"))?;
            ParsedTy::List(inner.into())
        }
        Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
        Rule::number_ref => ParsedTy::Primitive(PrimitiveTy::Number),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::any_ref => ParsedTy::Top,
        Rule::never_ref => ParsedTy::Bottom,
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
        Rule::EOI => return Ok(None),
        _ => {
            return Err(err_at_pair(
                format!("unexpected rule {:?} in type expression", curr.as_rule()),
                &curr,
            ));
        }
    };

    // Arrow chaining: right-associative lambdas.
    if let Some(lam_body) = collect_type_expr(pairs, ctx)? {
        return Ok(Some(ParsedTy::Lambda {
            param: curr.into(),
            body: lam_body.into(),
        }));
    }

    Ok(Some(curr))
}

fn collect_one(
    pair: pest::iterators::Pair<Rule>,
    ctx: &mut CollectCtx,
) -> Result<ParsedTy, CollectError> {
    match pair.as_rule() {
        Rule::isect_type => collect_intersection(pair.into_inner(), ctx),
        Rule::postfix_type => collect_postfix(pair.into_inner(), ctx),
        Rule::typeof_expr => collect_typeof(pair.into_inner()),
        Rule::import_type => collect_import_type(pair.into_inner()),
        Rule::applied_type => collect_applied_type(pair.into_inner(), ctx),
        Rule::atom_type
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref
        | Rule::arrow_segment
        | Rule::union_type
        | Rule::type_expr => collect_type_expr(pair.into_inner(), ctx)?
            .ok_or_else(|| CollectError::new("expected type expression, found empty")),
        Rule::attrset_type => collect_attrset(pair.into_inner(), ctx),
        Rule::list_type => {
            let inner = collect_type_expr(pair.into_inner(), ctx)?
                .ok_or_else(|| CollectError::new("list type has empty element type"))?;
            Ok(ParsedTy::List(inner.into()))
        }
        Rule::string_ref => Ok(ParsedTy::Primitive(PrimitiveTy::String)),
        Rule::number_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Number)),
        Rule::int_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Int)),
        Rule::bool_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Bool)),
        Rule::float_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Float)),
        Rule::path_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Path)),
        Rule::null_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Null)),
        Rule::any_ref => Ok(ParsedTy::Top),
        Rule::never_ref => Ok(ParsedTy::Bottom),
        Rule::generic_ident => Ok(ParsedTy::TyVar(TypeVarValue::Generic(pair.as_str().into()))),
        Rule::user_type => Ok(ParsedTy::TyVar(TypeVarValue::Reference(
            pair.as_str().into(),
        ))),
        _ => Err(err_at_pair(
            format!("unexpected rule {:?} in type expression", pair.as_rule()),
            &pair,
        )),
    }
}

/// Collect a postfix field access chain: `atom_type ("." field_access_key)*`.
fn collect_postfix(pairs: Pairs<Rule>, ctx: &mut CollectCtx) -> Result<ParsedTy, CollectError> {
    let mut iter = pairs;
    let base_pair = iter
        .next()
        .ok_or_else(|| CollectError::new("postfix_type missing base type"))?;
    let mut result = collect_one(base_pair, ctx)?;
    for key_pair in iter {
        if key_pair.as_rule() == Rule::field_access_key {
            result =
                ParsedTy::FieldAccess(ParsedTyRef::from(result), SmolStr::from(key_pair.as_str()));
        }
    }
    Ok(result)
}

/// Collect a typeof expression: `typeof_kw (import_path | identifier)`.
fn collect_typeof(pairs: Pairs<Rule>) -> Result<ParsedTy, CollectError> {
    let mut iter = pairs;
    // Skip typeof_kw
    let _kw = iter
        .next()
        .ok_or_else(|| CollectError::new("typeof_expr missing keyword"))?;
    let target = iter
        .next()
        .ok_or_else(|| CollectError::new("typeof_expr missing target"))?;
    match target.as_rule() {
        Rule::import_path => {
            let path = extract_import_path(target)?;
            Ok(ParsedTy::TypeOfImport(path))
        }
        Rule::identifier => Ok(ParsedTy::TypeOf(SmolStr::from(target.as_str()))),
        _ => Err(CollectError::new(format!(
            "unexpected rule {:?} in typeof_expr",
            target.as_rule()
        ))),
    }
}

/// Collect a cross-file type import: `import_kw "(" string_literal ")" "." user_type`.
fn collect_import_type(pairs: Pairs<Rule>) -> Result<ParsedTy, CollectError> {
    let mut iter = pairs;
    // Skip import_kw
    let _kw = iter
        .next()
        .ok_or_else(|| CollectError::new("import_type missing keyword"))?;
    let path_pair = iter
        .next()
        .ok_or_else(|| CollectError::new("import_type missing path"))?;
    let path = unquote_string_literal(path_pair.as_str());
    let type_name = iter
        .next()
        .ok_or_else(|| CollectError::new("import_type missing type name"))?;
    Ok(ParsedTy::ImportType(
        path,
        SmolStr::from(type_name.as_str()),
    ))
}

/// Collect an applied type: `type_func "(" type_expr ")"`.
fn collect_applied_type(
    pairs: Pairs<Rule>,
    ctx: &mut CollectCtx,
) -> Result<ParsedTy, CollectError> {
    let mut iter = pairs;
    let func = iter
        .next()
        .ok_or_else(|| CollectError::new("applied_type missing function"))?;
    let func_name = func.as_str();
    let inner = collect_type_expr(iter, ctx)?
        .ok_or_else(|| CollectError::new("applied_type missing inner type"))?;
    match func_name {
        "Param" => Ok(ParsedTy::Param(ParsedTyRef::from(inner))),
        "Return" => Ok(ParsedTy::Return(ParsedTyRef::from(inner))),
        _ => Err(CollectError::new(format!(
            "unknown type function: {func_name}"
        ))),
    }
}

/// Extract the path string from an import_path rule.
fn extract_import_path(pair: Pair<Rule>) -> Result<String, CollectError> {
    let mut iter = pair.into_inner();
    // Skip import_kw
    let _kw = iter
        .next()
        .ok_or_else(|| CollectError::new("import_path missing keyword"))?;
    let path_pair = iter
        .next()
        .ok_or_else(|| CollectError::new("import_path missing path"))?;
    Ok(unquote_string_literal(path_pair.as_str()))
}

/// Strip surrounding double quotes from a string literal.
fn unquote_string_literal(s: &str) -> String {
    s.trim_matches('"').to_string()
}

fn collect_union(pairs: Pairs<Rule>, ctx: &mut CollectCtx) -> Result<ParsedTy, CollectError> {
    let members: Result<Vec<ParsedTyRef>, CollectError> = pairs
        .map(|p| collect_one(p, ctx).map(ParsedTyRef::from))
        .collect();
    let mut members = members?;
    match members.len() {
        0 => Err(CollectError::new(
            "union type must have at least one member",
        )),
        1 => {
            let single = members.pop().expect("len checked above");
            Ok((*single.0).clone())
        }
        _ => Ok(ParsedTy::Union(members)),
    }
}

fn collect_intersection(
    pairs: Pairs<Rule>,
    ctx: &mut CollectCtx,
) -> Result<ParsedTy, CollectError> {
    let members: Result<Vec<ParsedTyRef>, CollectError> = pairs
        .map(|p| collect_one(p, ctx).map(ParsedTyRef::from))
        .collect();
    let mut members = members?;
    match members.len() {
        0 => Err(CollectError::new(
            "intersection type must have at least one member",
        )),
        1 => {
            let single = members.pop().expect("len checked above");
            Ok((*single.0).clone())
        }
        _ => Ok(ParsedTy::Intersection(members)),
    }
}

fn collect_attrset(pairs: Pairs<Rule>, ctx: &mut CollectCtx) -> Result<ParsedTy, CollectError> {
    let mut fields: BTreeMap<SmolStr, ParsedTyRef> = BTreeMap::new();
    let mut dyn_ty: Option<ParsedTyRef> = None;
    let mut open = false;
    let mut optional_fields = std::collections::BTreeSet::new();

    let parent_path = ctx.path().to_vec();

    for pair in pairs {
        match pair.as_rule() {
            Rule::named_field => {
                let mut inner = pair.into_inner();
                // Check for a doc_block on the field.
                let field_doc = take_doc_block(&mut inner);

                let name_pair = inner
                    .next()
                    .ok_or_else(|| CollectError::new("named_field missing field name"))?;
                // quoted_field includes surrounding quotes -- strip them.
                let name: SmolStr = match name_pair.as_rule() {
                    Rule::quoted_field => {
                        let raw = name_pair.as_str();
                        raw[1..raw.len() - 1].into()
                    }
                    _ => name_pair.as_str().into(),
                };

                // Check for optional_marker (`?` after the field name).
                if inner
                    .peek()
                    .is_some_and(|p| p.as_rule() == Rule::optional_marker)
                {
                    inner.next(); // consume the `?`
                    optional_fields.insert(name.clone());
                }

                // If this field has a doc comment, record it.
                if let Some(doc) = field_doc {
                    ctx.push_field_doc(name.clone(), doc);
                }

                // Set path context for nested attrsets so their field docs
                // get the correct prefix.
                let mut child_path = parent_path.clone();
                child_path.push(name.clone());
                ctx.set_path(child_path);

                let ty = collect_type_expr(inner, ctx)?
                    .ok_or_else(|| CollectError::new(format!("field '{name}' has empty type")))?;
                fields.insert(name, ty.into());

                // Restore parent path context.
                ctx.set_path(parent_path.clone());
            }
            Rule::dyn_field => {
                let inner = pair.into_inner();
                let ty = collect_type_expr(inner, ctx)?
                    .ok_or_else(|| CollectError::new("dynamic field has empty type"))?;
                dyn_ty = Some(ty.into());
            }
            Rule::open_marker => {
                open = true;
            }
            _ => {
                return Err(err_at_pair(
                    format!("unexpected rule {:?} in attrset type", pair.as_rule()),
                    &pair,
                ));
            }
        }
    }

    Ok(ParsedTy::AttrSet(AttrSetTy {
        fields,
        dyn_ty,
        open,
        optional_fields,
    }))
}

#[cfg(test)]
mod tests {
    use super::parse_source_loc;
    use crate::{known_ty, parse_tix_file};

    #[test]
    fn parse_source_loc_basic() {
        let loc = parse_source_loc("nixpkgs:lib/trivial.nix:61:8").unwrap();
        assert_eq!(loc.path.as_str(), "nixpkgs:lib/trivial.nix");
        assert_eq!(loc.line, 61);
        assert_eq!(loc.column, 8);
    }

    #[test]
    fn parse_source_loc_with_colons_in_path() {
        // Unlikely but handles paths with colons gracefully by splitting from right.
        let loc = parse_source_loc("nixpkgs:some:path:42:5").unwrap();
        assert_eq!(loc.path.as_str(), "nixpkgs:some:path");
        assert_eq!(loc.line, 42);
        assert_eq!(loc.column, 5);
    }

    #[test]
    fn parse_source_loc_invalid() {
        assert!(parse_source_loc("").is_none());
        assert!(parse_source_loc("just-a-path").is_none());
        assert!(parse_source_loc("path:notanumber:5").is_none());
    }

    #[test]
    fn type_alias() {
        let file = parse_tix_file("type Derivation = { name: string, system: string };")
            .expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias {
                name, body, doc, ..
            } => {
                assert_eq!(name.as_str(), "Derivation");
                assert_eq!(*body, known_ty!({ "name": string, "system": string }));
                assert_eq!(*doc, None);
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn val_decl() {
        let file = parse_tix_file("val mkDerivation :: { name: string, ... } -> { name: string };")
            .expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, ty, doc, .. } => {
                assert_eq!(name.as_str(), "mkDerivation");
                assert_eq!(
                    *ty,
                    known_ty!(({ "name": string; ... }) -> ({ "name": string }))
                );
                assert_eq!(*doc, None);
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn module_decl() {
        let src = r#"
            module lib {
                val id :: a -> a;
                module strings {
                    val concatStringsSep :: string -> [string] -> string;
                }
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::Module {
                name,
                declarations,
                doc,
                ..
            } => {
                assert_eq!(name.as_str(), "lib");
                assert_eq!(declarations.len(), 2);
                assert_eq!(*doc, None);

                // First: val id
                match &declarations[0] {
                    crate::TixDeclaration::ValDecl { name, ty, .. } => {
                        assert_eq!(name.as_str(), "id");
                        assert_eq!(*ty, known_ty!((# "a") -> (# "a")));
                    }
                    other => panic!("expected ValDecl, got: {other:?}"),
                }

                // Second: nested module
                match &declarations[1] {
                    crate::TixDeclaration::Module {
                        name, declarations, ..
                    } => {
                        assert_eq!(name.as_str(), "strings");
                        assert_eq!(declarations.len(), 1);
                    }
                    other => panic!("expected Module, got: {other:?}"),
                }
            }
            other => panic!("expected Module, got: {other:?}"),
        }
    }

    #[test]
    fn combined_file() {
        let src = r#"
            # A type alias
            type Nullable = a | null;

            # A val declaration
            val mkDerivation :: { name: string, ... } -> { name: string };

            # A module
            module lib {
                val id :: a -> a;
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");
        assert_eq!(file.declarations.len(), 3);
    }

    #[test]
    fn number_primitive_in_val() {
        let file = parse_tix_file("val add :: number -> number -> number;").expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, ty, .. } => {
                assert_eq!(name.as_str(), "add");
                assert_eq!(*ty, known_ty!(number -> number -> number));
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn generic_type_alias() {
        let file = parse_tix_file("type Nullable = a | null;").expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, body, .. } => {
                assert_eq!(name.as_str(), "Nullable");
                assert_eq!(*body, known_ty!(union!((# "a"), null)));
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn quoted_field_name() {
        let src = r#"type Sysctl = { "net.core.rmem_max": int, enable: bool, ... };"#;
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, body, .. } => {
                assert_eq!(name.as_str(), "Sysctl");
                match body {
                    crate::ParsedTy::AttrSet(attr) => {
                        // Quoted field should have quotes stripped in the parsed representation.
                        assert!(
                            attr.fields.contains_key("net.core.rmem_max"),
                            "expected 'net.core.rmem_max' field, got: {:?}",
                            attr.fields.keys().collect::<Vec<_>>()
                        );
                        assert!(attr.fields.contains_key("enable"));
                        assert!(attr.open);
                    }
                    other => panic!("expected AttrSet, got: {other:?}"),
                }
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    // =========================================================================
    // Doc comment tests
    // =========================================================================

    #[test]
    fn doc_comment_on_type_alias() {
        let src = "## A system configuration.\ntype Config = { ... };";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, doc, .. } => {
                assert_eq!(name.as_str(), "Config");
                assert_eq!(doc.as_deref(), Some("A system configuration."));
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn doc_comment_on_val_decl() {
        let src = "## Build a derivation.\nval mkDrv :: { ... } -> { ... };";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, doc, .. } => {
                assert_eq!(name.as_str(), "mkDrv");
                assert_eq!(doc.as_deref(), Some("Build a derivation."));
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn doc_comment_on_module() {
        let src = "## Library functions.\nmodule lib { val id :: a -> a; }";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::Module { name, doc, .. } => {
                assert_eq!(name.as_str(), "lib");
                assert_eq!(doc.as_deref(), Some("Library functions."));
            }
            other => panic!("expected Module, got: {other:?}"),
        }
    }

    #[test]
    fn multi_line_doc_comment() {
        let src = "## Line one.\n## Line two.\nval x :: int;";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { doc, .. } => {
                assert_eq!(doc.as_deref(), Some("Line one.\nLine two."));
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn doc_comment_on_field() {
        let src = r#"
            type Config = {
                ## Whether to enable.
                enable: bool,
                ...
            };
        "#;
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.field_docs.len(), 1);
        assert_eq!(
            file.field_docs[0].path,
            vec![
                smol_str::SmolStr::from("Config"),
                smol_str::SmolStr::from("enable")
            ]
        );
        assert_eq!(file.field_docs[0].doc.as_str(), "Whether to enable.");
    }

    #[test]
    fn doc_comment_mixed_with_regular_comments() {
        let src = r#"
            # Regular comment (ignored).
            ## Doc comment.
            val x :: int;
            # Another regular comment.
            val y :: string;
        "#;
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.declarations.len(), 2);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { doc, .. } => {
                assert_eq!(doc.as_deref(), Some("Doc comment."));
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
        match &file.declarations[1] {
            crate::TixDeclaration::ValDecl { doc, .. } => {
                assert_eq!(*doc, None);
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn nested_field_docs() {
        let src = r#"
            type Config = {
                ## Services section.
                services: {
                    ## Whether to enable SSH.
                    enable: bool,
                    ...
                },
                ...
            };
        "#;
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.field_docs.len(), 2);

        // First: Config.services
        assert_eq!(
            file.field_docs[0].path,
            vec![
                smol_str::SmolStr::from("Config"),
                smol_str::SmolStr::from("services")
            ]
        );
        assert_eq!(file.field_docs[0].doc.as_str(), "Services section.");

        // Second: Config.services.enable
        assert_eq!(
            file.field_docs[1].path,
            vec![
                smol_str::SmolStr::from("Config"),
                smol_str::SmolStr::from("services"),
                smol_str::SmolStr::from("enable"),
            ]
        );
        assert_eq!(file.field_docs[1].doc.as_str(), "Whether to enable SSH.");
    }

    // =========================================================================
    // Malformed .tix input error tests
    // =========================================================================

    #[test]
    fn missing_semicolon_is_parse_error() {
        // Missing trailing semicolon -- pest grammar should reject this.
        let result = parse_tix_file("type Foo = int");
        assert!(result.is_err(), "missing semicolon should produce an error");
        let err_msg = result.unwrap_err().to_string();
        // The error should be informative, not a panic.
        assert!(!err_msg.is_empty());
    }

    #[test]
    fn missing_type_body_is_error() {
        // `type Foo = ;` -- the grammar expects a type expression after `=`.
        let result = parse_tix_file("type Foo = ;");
        assert!(result.is_err(), "missing type body should produce an error");
    }

    #[test]
    fn missing_val_type_is_error() {
        // `val x :: ;` -- the grammar expects a type expression after `::`.
        let result = parse_tix_file("val x :: ;");
        assert!(result.is_err(), "missing val type should produce an error");
    }

    #[test]
    fn unclosed_brace_is_error() {
        let result = parse_tix_file("type Foo = { name: string ;");
        assert!(result.is_err(), "unclosed brace should produce an error");
    }

    #[test]
    fn unclosed_bracket_is_error() {
        let result = parse_tix_file("type Foo = [string ;");
        assert!(result.is_err(), "unclosed bracket should produce an error");
    }

    #[test]
    fn bad_type_keyword_is_error() {
        let result = parse_tix_file("tyep Foo = int;");
        assert!(result.is_err(), "misspelled 'type' should produce an error");
    }

    #[test]
    fn empty_module_is_ok() {
        // An empty module is syntactically valid.
        let result = parse_tix_file("module empty { }");
        assert!(result.is_ok(), "empty module should parse: {result:?}");
    }

    #[test]
    fn unclosed_module_brace_is_error() {
        let result = parse_tix_file("module lib { val id :: a -> a;");
        assert!(
            result.is_err(),
            "unclosed module brace should produce an error"
        );
    }

    #[test]
    fn tix_error_display_includes_context() {
        // Verify that TixError::Parse includes the pest error message.
        let err = parse_tix_file("type Foo = ;").unwrap_err();
        let msg = err.to_string();
        assert!(!msg.is_empty(), "error message should not be empty");
    }

    // =========================================================================
    // any/never keyword tests
    // =========================================================================

    #[test]
    fn any_keyword_parses_to_top() {
        let file = parse_tix_file("val f :: any -> int;").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { ty, .. } => match ty {
                crate::ParsedTy::Lambda { param, .. } => {
                    assert_eq!(*param.0, crate::ParsedTy::Top);
                }
                other => panic!("expected Lambda, got: {other:?}"),
            },
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn never_keyword_parses_to_bottom() {
        let file = parse_tix_file("val f :: int -> never;").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { ty, .. } => match ty {
                crate::ParsedTy::Lambda { body, .. } => {
                    assert_eq!(*body.0, crate::ParsedTy::Bottom);
                }
                other => panic!("expected Lambda, got: {other:?}"),
            },
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn any_in_union_position() {
        let file = parse_tix_file("type T = int | any;").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { body, .. } => match body {
                crate::ParsedTy::Union(members) => {
                    assert!(
                        members.iter().any(|m| *m.0 == crate::ParsedTy::Top),
                        "union should contain Top (any)"
                    );
                }
                other => panic!("expected Union, got: {other:?}"),
            },
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn any_in_intersection_position() {
        let file = parse_tix_file("type T = int & any;").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { body, .. } => match body {
                crate::ParsedTy::Intersection(members) => {
                    assert!(
                        members.iter().any(|m| *m.0 == crate::ParsedTy::Top),
                        "intersection should contain Top (any)"
                    );
                }
                other => panic!("expected Intersection, got: {other:?}"),
            },
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    // =========================================================================
    // Optional field syntax tests
    // =========================================================================

    #[test]
    fn optional_field_basic() {
        let file = parse_tix_file("type T = { x?: int };").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { body, .. } => match body {
                crate::ParsedTy::AttrSet(attr) => {
                    assert!(attr.fields.contains_key("x"), "should have field 'x'");
                    assert!(
                        attr.optional_fields.contains("x"),
                        "field 'x' should be optional"
                    );
                }
                other => panic!("expected AttrSet, got: {other:?}"),
            },
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn mixed_optional_and_required_fields() {
        let file = parse_tix_file("type T = { x?: int, y: string };").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { body, .. } => match body {
                crate::ParsedTy::AttrSet(attr) => {
                    assert!(attr.fields.contains_key("x"));
                    assert!(attr.fields.contains_key("y"));
                    assert!(attr.optional_fields.contains("x"), "x should be optional");
                    assert!(!attr.optional_fields.contains("y"), "y should be required");
                }
                other => panic!("expected AttrSet, got: {other:?}"),
            },
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn optional_field_with_any_type() {
        let file = parse_tix_file("type T = { x?: any };").expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { body, .. } => match body {
                crate::ParsedTy::AttrSet(attr) => {
                    assert!(attr.optional_fields.contains("x"));
                    assert_eq!(
                        *attr.fields["x"].0,
                        crate::ParsedTy::Top,
                        "optional field 'x' should have type any (Top)"
                    );
                }
                other => panic!("expected AttrSet, got: {other:?}"),
            },
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    // =========================================================================
    // Span capture tests
    // =========================================================================

    #[test]
    fn type_alias_span_captured() {
        let src = "type Foo = int;";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { span, .. } => {
                assert_eq!(*span, (0, src.len()));
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn module_span_captured() {
        let src = "module lib { val id :: a -> a; }";
        let file = parse_tix_file(src).expect("parse error");

        match &file.declarations[0] {
            crate::TixDeclaration::Module { span, .. } => {
                assert_eq!(*span, (0, src.len()));
            }
            other => panic!("expected Module, got: {other:?}"),
        }
    }

    #[test]
    fn spans_in_multi_decl_file() {
        let src = "type A = int;\ntype B = string;";
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.declarations.len(), 2);

        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, span, .. } => {
                assert_eq!(name.as_str(), "A");
                assert_eq!(&src[span.0..span.1], "type A = int;");
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }

        match &file.declarations[1] {
            crate::TixDeclaration::TypeAlias { name, span, .. } => {
                assert_eq!(name.as_str(), "B");
                assert_eq!(&src[span.0..span.1], "type B = string;");
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    // =========================================================================
    // @source annotation tests
    // =========================================================================

    #[test]
    fn source_annotation_on_val() {
        let src = r#"
            @source nixpkgs:lib/trivial.nix:61:8
            val id :: a -> a;
        "#;
        let file = parse_tix_file(src).expect("parse error");
        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, source, .. } => {
                assert_eq!(name.as_str(), "id");
                let src_loc = source.as_ref().expect("should have source location");
                assert_eq!(src_loc.path.as_str(), "nixpkgs:lib/trivial.nix");
                assert_eq!(src_loc.line, 61);
                assert_eq!(src_loc.column, 8);
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn source_annotation_with_doc_block() {
        let src = r#"
            ## The identity function.
            @source nixpkgs:lib/trivial.nix:61:8
            val id :: a -> a;
        "#;
        let file = parse_tix_file(src).expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl {
                name, doc, source, ..
            } => {
                assert_eq!(name.as_str(), "id");
                assert_eq!(doc.as_deref(), Some("The identity function."));
                let src_loc = source.as_ref().expect("should have source location");
                assert_eq!(src_loc.path.as_str(), "nixpkgs:lib/trivial.nix");
                assert_eq!(src_loc.line, 61);
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn source_annotation_on_module() {
        let src = r#"
            @source nixpkgs:lib/default.nix:59:7
            module lib {
                val id :: a -> a;
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::Module {
                name,
                source,
                declarations,
                ..
            } => {
                assert_eq!(name.as_str(), "lib");
                let src_loc = source.as_ref().expect("should have source location");
                assert_eq!(src_loc.path.as_str(), "nixpkgs:lib/default.nix");
                assert_eq!(declarations.len(), 1);
            }
            other => panic!("expected Module, got: {other:?}"),
        }
    }

    #[test]
    fn source_annotation_on_type_alias() {
        let src = r#"
            @source nixpkgs:lib/types.nix:10:3
            type Derivation = { name: string };
        "#;
        let file = parse_tix_file(src).expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, source, .. } => {
                assert_eq!(name.as_str(), "Derivation");
                let src_loc = source.as_ref().expect("should have source location");
                assert_eq!(src_loc.path.as_str(), "nixpkgs:lib/types.nix");
                assert_eq!(src_loc.line, 10);
                assert_eq!(src_loc.column, 3);
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn no_source_annotation_backward_compat() {
        let src = "val id :: a -> a;";
        let file = parse_tix_file(src).expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { source, .. } => {
                assert!(source.is_none(), "should have no source location");
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn source_annotation_home_manager_path() {
        let src = r#"
            @source home-manager:modules/programs/git.nix:15:3
            val enable :: bool;
        "#;
        let file = parse_tix_file(src).expect("parse error");
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { source, .. } => {
                let src_loc = source.as_ref().expect("should have source location");
                assert_eq!(
                    src_loc.path.as_str(),
                    "home-manager:modules/programs/git.nix"
                );
                assert_eq!(src_loc.line, 15);
                assert_eq!(src_loc.column, 3);
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }
}
