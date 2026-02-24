mod collect;
pub mod tix_collect;
pub mod tix_parser;

use std::fmt;
use std::sync::Arc;

use collect::collect_type_decls;
use derive_more::Debug;
use lang_ty::{AttrSetTy, PrimitiveTy};
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;
use smol_str::SmolStr;

#[derive(Parser)]
#[grammar = "comment.pest"]
pub struct CommentParser;

// Box the error since the raw pest error type is large (clippy::result_large_err).
type ParseError = Box<pest::error::Error<Rule>>;

// =============================================================================
// Stub collection error type
// =============================================================================
//
// Errors that occur during collection (walking the pest parse tree to produce
// structured types). These are distinct from *parse* errors -- the grammar
// accepted the input, but the collector encountered an unexpected rule or
// structural invariant violation. In practice this means a bug in the grammar
// or a new rule that the collector doesn't handle yet.

/// An error encountered while collecting types from a parsed `.tix` file or
/// doc comment. Carries a human-readable message and, where available, the
/// byte span in the source that triggered the error.
#[derive(Clone, PartialEq, Eq)]
pub struct CollectError {
    pub message: String,
    /// Byte offset range in the original source, if available.
    pub span: Option<(usize, usize)>,
}

impl CollectError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    pub fn with_span(message: impl Into<String>, start: usize, end: usize) -> Self {
        Self {
            message: message.into(),
            span: Some((start, end)),
        }
    }
}

impl fmt::Debug for CollectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((start, end)) = self.span {
            write!(f, "CollectError({}, {}..{})", self.message, start, end)
        } else {
            write!(f, "CollectError({})", self.message)
        }
    }
}

impl fmt::Display for CollectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((start, end)) = self.span {
            write!(f, "{} (at bytes {}..{})", self.message, start, end)
        } else {
            write!(f, "{}", self.message)
        }
    }
}

impl std::error::Error for CollectError {}

/// Combined error type for `.tix` file processing, covering both the pest
/// parsing phase and the collection phase.
#[derive(Debug)]
pub enum TixError {
    /// The pest grammar rejected the input.
    Parse(Box<pest::error::Error<tix_parser::Rule>>),
    /// The parse tree was structurally invalid during collection.
    Collect(CollectError),
}

impl fmt::Display for TixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TixError::Parse(e) => write!(f, "{e}"),
            TixError::Collect(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for TixError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            TixError::Parse(e) => Some(e.as_ref()),
            TixError::Collect(e) => Some(e),
        }
    }
}

impl From<CollectError> for TixError {
    fn from(e: CollectError) -> Self {
        TixError::Collect(e)
    }
}

impl From<Box<pest::error::Error<tix_parser::Rule>>> for TixError {
    fn from(e: Box<pest::error::Error<tix_parser::Rule>>) -> Self {
        TixError::Parse(e)
    }
}

pub fn parse_comment_text(source: &str) -> Result<Pairs<'_, Rule>, ParseError> {
    Ok(CommentParser::parse(Rule::comment_content, source)?)
}

// TODO: might worth adding this as salsa query
pub fn parse_and_collect(source: &str) -> Result<Vec<TypeDecl>, ParseError> {
    let pairs = parse_comment_text(source)?;

    Ok(collect_type_decls(pairs))
}

// =============================================================================
// Context annotation parsing
// =============================================================================

/// Parse a `context: <name>` annotation from a doc comment string.
///
/// A doc comment like `/** context: nixos */` is stored as the string
/// `"context: nixos"` after the leading `/**` and trailing `*/` are stripped.
/// This function extracts the context name from such a string.
pub fn parse_context_annotation(doc: &str) -> Option<SmolStr> {
    let trimmed = doc.trim();
    let rest = trimmed.strip_prefix("context:")?;
    let name = rest.trim();
    if name.is_empty() {
        None
    } else {
        Some(SmolStr::from(name))
    }
}

// =============================================================================
// .tix declaration file types and parsing
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TixDeclFile {
    pub declarations: Vec<TixDeclaration>,
    /// Field-level doc comments collected during parsing, with dotted paths
    /// from the parent type alias (e.g. `["NixosConfig", "services", "enable"]`).
    pub field_docs: Vec<FieldDoc>,
}

/// A doc comment attached to a field inside a type alias body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDoc {
    /// Path from the root type alias to the field (e.g. `["NixosConfig", "services", "enable"]`).
    pub path: Vec<SmolStr>,
    pub doc: SmolStr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TixDeclaration {
    TypeAlias {
        name: SmolStr,
        body: ParsedTy,
        doc: Option<SmolStr>,
    },
    ValDecl {
        name: SmolStr,
        ty: ParsedTy,
        doc: Option<SmolStr>,
    },
    Module {
        name: SmolStr,
        declarations: Vec<TixDeclaration>,
        doc: Option<SmolStr>,
    },
}

/// Try to parse a doc comment string as an inline type alias declaration.
/// Returns `Some((name, body))` if the string matches `type Name = ...;`.
/// Returns `None` if it doesn't look like a type alias.
///
/// Reuses the existing `.tix` parser — no new grammar needed.
pub fn parse_inline_type_alias(source: &str) -> Option<(SmolStr, ParsedTy)> {
    let trimmed = source.trim();
    if !trimmed.starts_with("type ")
        || !trimmed
            .as_bytes()
            .get(5)
            .is_some_and(|b| b.is_ascii_uppercase())
    {
        return None;
    }
    let file = parse_tix_file(trimmed).ok()?;
    file.declarations.into_iter().find_map(|decl| match decl {
        TixDeclaration::TypeAlias { name, body, .. } => Some((name, body)),
        _ => None,
    })
}

pub fn parse_tix_file(source: &str) -> Result<TixDeclFile, TixError> {
    use pest::Parser;
    let pairs = tix_parser::TixDeclParser::parse(tix_parser::Rule::tix_file, source)
        .map_err(|e| TixError::Parse(Box::new(e)))?;
    tix_collect::collect_tix_file(pairs).map_err(TixError::Collect)
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeDecl {
    pub identifier: SmolStr,
    pub type_expr: ParsedTy,
}

// =============================================================================
// Parsed type representation
// =============================================================================
//
// Standalone enum for types parsed from doc comment annotations. Includes all
// seven variants (the five from Ty<R> plus Union and Intersection) so that
// comment annotations can express the full type language. This mirrors OutputTy
// conceptually but uses TypeVarValue for type variables (named generics and
// references) instead of numeric IDs.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParsedTyRef(pub Arc<ParsedTy>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParsedTy {
    TyVar(TypeVarValue),
    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),
    #[debug("List({_0:?})")]
    List(ParsedTyRef),
    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda {
        param: ParsedTyRef,
        body: ParsedTyRef,
    },
    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<ParsedTyRef>),
    #[debug("Union({_0:?})")]
    Union(Vec<ParsedTyRef>),
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<ParsedTyRef>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeVarValue {
    Generic(SmolStr),   // A generic with a given identifier
    Reference(SmolStr), // A reference to a different Type, should be resolved during checking
}

impl From<ParsedTy> for ParsedTyRef {
    fn from(value: ParsedTy) -> Self {
        ParsedTyRef(Arc::new(value))
    }
}

impl ParsedTy {
    /// Collect all free type variables in this type.
    pub fn free_vars(&self) -> std::collections::HashSet<TypeVarValue> {
        let mut set = std::collections::HashSet::new();
        self.collect_free_vars(&mut set);
        set
    }

    fn collect_free_vars(&self, set: &mut std::collections::HashSet<TypeVarValue>) {
        match self {
            ParsedTy::TyVar(var) => {
                set.insert(var.clone());
            }
            ParsedTy::Primitive(_) => {}
            ParsedTy::List(inner) => inner.0.collect_free_vars(set),
            ParsedTy::Lambda { param, body } => {
                param.0.collect_free_vars(set);
                body.0.collect_free_vars(set);
            }
            ParsedTy::AttrSet(attr) => {
                for v in attr.fields.values() {
                    v.0.collect_free_vars(set);
                }
                if let Some(dyn_ty) = &attr.dyn_ty {
                    dyn_ty.0.collect_free_vars(set);
                }
            }
            ParsedTy::Union(members) | ParsedTy::Intersection(members) => {
                for m in members {
                    m.0.collect_free_vars(set);
                }
            }
        }
    }

    /// Rename all `Generic` type variables by appending a suffix.
    /// Each `val` declaration in a `.tix` module should have independently
    /// scoped type variables — `a` in `val id :: a -> a` must be independent
    /// from `a` in `val warn :: string -> a -> a`. This method renames
    /// generics so they don't collide when multiple `val` types are combined
    /// into a single module attrset.
    pub fn rename_generics(&self, suffix: &str) -> ParsedTy {
        match self {
            ParsedTy::TyVar(TypeVarValue::Generic(name)) => ParsedTy::TyVar(TypeVarValue::Generic(
                SmolStr::from(format!("{name}${suffix}")),
            )),
            ParsedTy::TyVar(_) | ParsedTy::Primitive(_) => self.clone(),
            ParsedTy::List(inner) => {
                ParsedTy::List(ParsedTyRef::from(inner.0.rename_generics(suffix)))
            }
            ParsedTy::Lambda { param, body } => ParsedTy::Lambda {
                param: ParsedTyRef::from(param.0.rename_generics(suffix)),
                body: ParsedTyRef::from(body.0.rename_generics(suffix)),
            },
            ParsedTy::AttrSet(attr) => {
                let fields = attr
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), ParsedTyRef::from(v.0.rename_generics(suffix))))
                    .collect();
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| ParsedTyRef::from(d.0.rename_generics(suffix)));
                ParsedTy::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            ParsedTy::Union(members) => ParsedTy::Union(
                members
                    .iter()
                    .map(|m| ParsedTyRef::from(m.0.rename_generics(suffix)))
                    .collect(),
            ),
            ParsedTy::Intersection(members) => ParsedTy::Intersection(
                members
                    .iter()
                    .map(|m| ParsedTyRef::from(m.0.rename_generics(suffix)))
                    .collect(),
            ),
        }
    }

    /// Returns true if this type contains any `Union` nodes. Used to detect
    /// annotations that require narrowing support (e.g. `string | [string]`
    /// as a function parameter) and skip them rather than producing false
    /// type errors.
    pub fn contains_union(&self) -> bool {
        match self {
            ParsedTy::Union(_) => true,
            ParsedTy::TyVar(_) | ParsedTy::Primitive(_) => false,
            ParsedTy::List(inner) => inner.0.contains_union(),
            ParsedTy::Lambda { param, body } => param.0.contains_union() || body.0.contains_union(),
            ParsedTy::AttrSet(attr) => {
                attr.fields.values().any(|v| v.0.contains_union())
                    || attr.dyn_ty.as_ref().is_some_and(|d| d.0.contains_union())
            }
            ParsedTy::Intersection(members) => members.iter().any(|m| m.0.contains_union()),
        }
    }

    /// Returns true if this type is an intersection where every member is a
    /// lambda. Such annotations declare overloaded function types that can't
    /// be verified against a single lambda body with bidirectional constraints.
    pub fn is_intersection_of_lambdas(&self) -> bool {
        match self {
            ParsedTy::Intersection(members) => members
                .iter()
                .all(|m| matches!(&*m.0, ParsedTy::Lambda { .. })),
            _ => false,
        }
    }
}

// TODO: Structurally duplicated from `arc_ty!` in `lang_ty`. If more variants
// are added, consider extracting a shared `impl_ty_macro!` helper.
#[macro_export]
macro_rules! known_ty {
    // -- Match on known primitives -----------------------------------------
    (null) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Null)
    };
    (bool) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Bool)
    };
    (int) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Int)
    };
    (number) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Number)
    };
    (float) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Float)
    };
    (string) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::String)
    };
    (path) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Path)
    };
    (uri) => {
        $crate::ParsedTy::Primitive(::lang_ty::PrimitiveTy::Uri)
    };
    // -- TyVar syntax: (# "a") for generic type variables ------------------
    (# $e:expr) => {
        $crate::ParsedTy::TyVar($crate::TypeVarValue::Generic(($e).into()))
    };

    (($($inner:tt)*)) => { $crate::known_ty!($($inner)*) };
    ([$($inner:tt)*]) => { $crate::ParsedTy::List($crate::ParsedTyRef::from($crate::known_ty!($($inner)*)))};

    // -- Union: union!(ty1, ty2, ...) --------------------------------------
    (union!($($member:tt),+ $(,)?)) => {{
        $crate::ParsedTy::Union(vec![
            $($crate::ParsedTyRef::from($crate::known_ty!($member)),)+
        ])
    }};

    // -- Intersection: isect!(ty1, ty2, ...) --------------------------------
    (isect!($($member:tt),+ $(,)?)) => {{
        $crate::ParsedTy::Intersection(vec![
            $($crate::ParsedTyRef::from($crate::known_ty!($member)),)+
        ])
    }};

    // -- Closed attrset: { "key": ty, ... } ---------------------------------
    ({ $($key:literal : $ty:tt),* $(,)? }) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: [
                $((::smol_str::SmolStr::from($key), $crate::ParsedTyRef::from($crate::known_ty!($ty))),)*
            ].into_iter().collect(),
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        })
    }};

    // -- Open attrset: { "key": ty, ... ; ... } ----------------------------
    ({ $($key:literal : $ty:tt),* $(,)?; ... }) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: [
                $((::smol_str::SmolStr::from($key), $crate::ParsedTyRef::from($crate::known_ty!($ty))),)*
            ].into_iter().collect(),
            dyn_ty: None,
            open: true,
            optional_fields: std::collections::BTreeSet::new(),
        })
    }};

    // -- Dyn attrset: dyn_attrset!(dyn_ty) --------------------------------
    (dyn_attrset!($dyn_ty:tt)) => {{
        $crate::ParsedTy::AttrSet(::lang_ty::AttrSetTy {
            fields: std::collections::BTreeMap::new(),
            dyn_ty: Some($crate::ParsedTyRef::from($crate::known_ty!($dyn_ty))),
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        })
    }};

    // -- Lambda: arg -> ret ------------------------------------------------
    ($arg:tt -> $($ret:tt)*) => {
        $crate::ParsedTy::Lambda {
            param: $crate::ParsedTyRef::from($crate::known_ty!($arg)),
            body: $crate::ParsedTyRef::from($crate::known_ty!($($ret)*)),
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_annotation_valid() {
        assert_eq!(
            parse_context_annotation("context: nixos"),
            Some(SmolStr::from("nixos"))
        );
    }

    #[test]
    fn context_annotation_with_whitespace() {
        assert_eq!(
            parse_context_annotation("  context:   home-manager  "),
            Some(SmolStr::from("home-manager"))
        );
    }

    #[test]
    fn context_annotation_no_prefix() {
        assert_eq!(parse_context_annotation("type: x :: int"), None);
    }

    #[test]
    fn context_annotation_empty_name() {
        assert_eq!(parse_context_annotation("context:   "), None);
    }

    #[test]
    fn context_annotation_bare_prefix() {
        assert_eq!(parse_context_annotation("context:"), None);
    }

    #[test]
    fn inline_alias_basic() {
        let result = parse_inline_type_alias("type Pair = { fst: a, snd: b };");
        assert!(result.is_some());
        let (name, body) = result.unwrap();
        assert_eq!(name.as_str(), "Pair");
        assert!(matches!(body, ParsedTy::AttrSet(_)));
    }

    #[test]
    fn inline_alias_with_whitespace() {
        let result = parse_inline_type_alias("  type Nullable = a | null;  ");
        assert!(result.is_some());
        let (name, _) = result.unwrap();
        assert_eq!(name.as_str(), "Nullable");
    }

    #[test]
    fn inline_alias_not_a_binding_annotation() {
        // "type:" (colon) is a binding annotation, not an alias
        assert!(parse_inline_type_alias("type: x :: int").is_none());
    }

    #[test]
    fn inline_alias_lowercase_rejected() {
        // Lowercase after "type " is a generic var, not an alias name
        assert!(parse_inline_type_alias("type foo = int;").is_none());
    }

    #[test]
    fn inline_alias_not_a_comment() {
        // Regular text that doesn't start with "type "
        assert!(parse_inline_type_alias("hello world").is_none());
    }
}

// =============================================================================
// Conformance tests: collect.rs ↔ tix_collect.rs
// =============================================================================
//
// Both parsers share type expression syntax but use different pest grammars.
// These tests verify that identical type expression strings produce the same
// `ParsedTy` through both paths, catching accidental divergence when one
// file is updated without the other.

#[cfg(test)]
mod conformance_tests {
    use super::*;

    /// Parse a type expression through the doc comment parser (collect.rs).
    /// Wraps the expression in a `type: x :: <expr>` doc comment.
    fn parse_via_comment(expr: &str) -> ParsedTy {
        let comment = format!("type: x :: {expr}");
        let pairs = parse_comment_text(&comment).expect("comment parse error");
        let decls = collect::collect_type_decls(pairs);
        assert_eq!(decls.len(), 1, "expected exactly one decl for: {expr}");
        decls.into_iter().next().unwrap().type_expr
    }

    /// Parse a type expression through the .tix parser (tix_collect.rs).
    /// Wraps the expression in a `val x :: <expr>;` declaration.
    fn parse_via_tix(expr: &str) -> ParsedTy {
        let tix = format!("val x :: {expr};");
        let file = parse_tix_file(&tix).unwrap_or_else(|e| {
            panic!("tix parse error for '{expr}': {e}");
        });
        assert_eq!(
            file.declarations.len(),
            1,
            "expected exactly one decl for: {expr}"
        );
        match file.declarations.into_iter().next().unwrap() {
            TixDeclaration::ValDecl { ty, .. } => ty,
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    /// Assert both parsers produce the same ParsedTy for the given expression.
    fn assert_conformance(expr: &str) {
        let comment_ty = parse_via_comment(expr);
        let tix_ty = parse_via_tix(expr);
        assert_eq!(
            comment_ty, tix_ty,
            "parsers diverged for: {expr}\n  comment: {comment_ty:?}\n  tix:     {tix_ty:?}"
        );
    }

    #[test]
    fn primitives() {
        for prim in ["int", "string", "bool", "float", "path", "null", "number"] {
            assert_conformance(prim);
        }
    }

    #[test]
    fn generic_vars() {
        assert_conformance("a");
        assert_conformance("b");
    }

    #[test]
    fn type_references() {
        assert_conformance("Derivation");
        assert_conformance("Lib");
    }

    #[test]
    fn list_types() {
        assert_conformance("[int]");
        assert_conformance("[a]");
        assert_conformance("[[string]]");
    }

    #[test]
    fn lambda_types() {
        assert_conformance("a -> b");
        assert_conformance("int -> string -> bool");
        assert_conformance("(a -> b) -> a -> b");
    }

    #[test]
    fn union_types() {
        assert_conformance("int | string");
        assert_conformance("int | string | null");
    }

    #[test]
    fn intersection_types() {
        assert_conformance("a & b");
        assert_conformance("a & b & c");
    }

    #[test]
    fn attrset_closed() {
        assert_conformance("{ name: string, age: int }");
    }

    #[test]
    fn attrset_open() {
        assert_conformance("{ name: string, ... }");
    }

    #[test]
    fn attrset_dyn() {
        assert_conformance("{ _: int }");
    }

    #[test]
    fn attrset_only_open() {
        assert_conformance("{ ... }");
    }

    #[test]
    fn complex_combinations() {
        assert_conformance("{ name: string, ... } -> Derivation");
        assert_conformance("[a] -> (a -> b) -> [b]");
        assert_conformance("int | string -> bool");
        assert_conformance("int & bool | string");
        assert_conformance("(int -> int) | (string -> string)");
        assert_conformance("{ _: int | null }");
    }
}
