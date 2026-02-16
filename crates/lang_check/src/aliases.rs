// ==============================================================================
// Type Alias Registry
// ==============================================================================
//
// Holds type aliases and global val declarations loaded from .tix stub files.
// `TypeAliasRegistry` is built before inference begins and passed into `CheckCtx`
// so that `TypeVarValue::Reference` names resolve against loaded aliases, and
// unresolved names can fall back to global val declarations.

use std::collections::HashMap;
use std::path::PathBuf;

use comment_parser::{ParsedTy, ParsedTyRef, TixDeclFile, TixDeclaration};
use lang_ty::AttrSetTy;
use smol_str::SmolStr;

const BUILTIN_STUBS: &str = include_str!("../../../stubs/lib.tix");
const NIXOS_CONTEXT_STUBS: &str = include_str!("../../../stubs/contexts/nixos.tix");
const HM_CONTEXT_STUBS: &str = include_str!("../../../stubs/contexts/home-manager.tix");

// =============================================================================
// DocIndex — documentation storage for .tix declarations and fields
// =============================================================================
//
// Stores doc comments extracted from .tix stub files so they can be surfaced
// in LSP hover and other features. Separate from the type data in the registry
// because docs are presentation-layer and not needed during inference.

#[derive(Debug, Clone, Default)]
pub struct DocIndex {
    /// Docs for top-level declarations (type aliases, vals, modules) by name.
    decl_docs: HashMap<SmolStr, SmolStr>,

    /// Docs for fields within type aliases.
    /// Key: alias name (e.g. "NixosConfig"), Value: field path → doc.
    /// Field path is relative to the alias (e.g. ["services", "enable"]).
    field_docs: HashMap<SmolStr, HashMap<Vec<SmolStr>, SmolStr>>,
}

impl DocIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up the doc comment for a top-level declaration by name.
    pub fn decl_doc(&self, name: &str) -> Option<&SmolStr> {
        self.decl_docs.get(name)
    }

    /// Look up the doc comment for a field within a type alias.
    /// `alias` is the type alias name (e.g. "NixosConfig").
    /// `path` is the dotted path to the field (e.g. ["services", "enable"]).
    pub fn field_doc(&self, alias: &str, path: &[SmolStr]) -> Option<&SmolStr> {
        self.field_docs.get(alias)?.get(path)
    }

    /// Insert a declaration-level doc.
    fn insert_decl_doc(&mut self, name: SmolStr, doc: SmolStr) {
        self.decl_docs.insert(name, doc);
    }

    /// Insert a field-level doc.
    fn insert_field_doc(&mut self, alias: SmolStr, path: Vec<SmolStr>, doc: SmolStr) {
        self.field_docs.entry(alias).or_default().insert(path, doc);
    }
}

// =============================================================================
// TypeAliasRegistry
// =============================================================================

#[derive(Debug, Clone, Default)]
pub struct TypeAliasRegistry {
    /// Type alias name -> body (e.g. `Derivation` -> `{ name: string, ... }`)
    aliases: HashMap<SmolStr, ParsedTy>,

    /// Top-level val declarations (e.g. `mkDerivation` -> `{ name: string, ... } -> Derivation`)
    global_vals: HashMap<SmolStr, ParsedTy>,

    /// Documentation extracted from .tix stub files.
    pub docs: DocIndex,

    /// Override directory for built-in context stubs. When set,
    /// `load_context_by_name("nixos")` checks for `<dir>/nixos.tix` before
    /// falling back to the compiled-in minimal stubs. Set via the
    /// `TIX_BUILTIN_STUBS` environment variable.
    builtin_stubs_dir: Option<PathBuf>,
}

/// Controls where val declarations are routed during `load_declarations`.
enum ValTarget<'a> {
    /// Store in the registry's `global_vals` map (normal .tix file loading).
    GlobalVals,
    /// Collect into a separate map (context stub loading).
    ContextArgs(&'a mut HashMap<SmolStr, ParsedTy>),
}

impl TypeAliasRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a registry pre-loaded with the shipped nixpkgs stubs.
    pub fn with_builtins() -> Self {
        let mut registry = Self::new();
        match comment_parser::parse_tix_file(BUILTIN_STUBS) {
            Ok(file) => registry.load_tix_file(&file),
            Err(e) => log::warn!("Failed to parse builtin stubs: {e}"),
        }
        registry
    }

    /// Set the override directory for built-in context stubs.
    /// When resolving `@nixos` or `/** context: nixos */`, the registry
    /// will check for `<dir>/nixos.tix` before falling back to the
    /// compiled-in minimal stubs.
    pub fn set_builtin_stubs_dir(&mut self, dir: PathBuf) {
        self.builtin_stubs_dir = Some(dir);
    }

    /// Load declarations from a parsed .tix file into the registry.
    pub fn load_tix_file(&mut self, file: &TixDeclFile) {
        let mut target = ValTarget::GlobalVals;
        self.load_declarations(&file.declarations, &mut target);
        self.load_field_docs(&file.field_docs);
    }

    /// Recursively load declarations. `val_target` controls where val
    /// declarations are routed: `GlobalVals` adds them to the registry's
    /// `global_vals` map; `ContextArgs` collects them into a separate map
    /// for context-scoped parameters.
    fn load_declarations(
        &mut self,
        declarations: &[TixDeclaration],
        val_target: &mut ValTarget<'_>,
    ) {
        for decl in declarations {
            match decl {
                TixDeclaration::TypeAlias { name, body, doc } => {
                    self.aliases.insert(name.clone(), body.clone());
                    if let Some(doc) = doc {
                        self.docs.insert_decl_doc(name.clone(), doc.clone());
                    }
                }
                TixDeclaration::ValDecl { name, ty, doc } => {
                    match val_target {
                        ValTarget::GlobalVals => {
                            self.global_vals.insert(name.clone(), ty.clone());
                        }
                        ValTarget::ContextArgs(ref mut map) => {
                            map.insert(name.clone(), ty.clone());
                        }
                    }
                    if let Some(doc) = doc {
                        self.docs.insert_decl_doc(name.clone(), doc.clone());
                    }
                }
                TixDeclaration::Module {
                    name,
                    declarations,
                    doc,
                } => {
                    // Convert the module into an attrset type and register it
                    // as a type alias with the capitalized module name.
                    // e.g. `module lib { val id :: a -> a; }` -> alias "Lib" = { id: a -> a, ... }
                    let new_attrset = module_to_attrset(declarations);
                    let alias_name = capitalize(name);

                    // If the alias already exists as an attrset (from a previous
                    // stub file declaring the same module), merge fields instead
                    // of silently overwriting. This allows splitting large module
                    // declarations across multiple .tix files.
                    let merged = match (self.aliases.get(&alias_name), &new_attrset) {
                        (Some(ParsedTy::AttrSet(existing)), ParsedTy::AttrSet(new)) => {
                            ParsedTy::AttrSet(merge_parsed_attrsets(existing, new))
                        }
                        _ => new_attrset,
                    };
                    self.aliases.insert(alias_name.clone(), merged);

                    if let Some(doc) = doc {
                        self.docs.insert_decl_doc(alias_name.clone(), doc.clone());
                    }

                    // Module val docs become field docs on the capitalized alias.
                    // e.g. `module lib { ## identity fn \n val id :: a -> a; }` →
                    //   field doc on Lib.id
                    self.collect_module_field_docs(&alias_name, declarations, &[]);
                }
            }
        }
    }

    /// Load field-level doc comments from a parsed .tix file into the doc index.
    fn load_field_docs(&mut self, field_docs: &[comment_parser::FieldDoc]) {
        for field_doc in field_docs {
            if field_doc.path.len() >= 2 {
                let alias = field_doc.path[0].clone();
                let field_path = field_doc.path[1..].to_vec();
                self.docs
                    .insert_field_doc(alias, field_path, field_doc.doc.clone());
            }
        }
    }

    /// Recursively collect doc comments from module val declarations and
    /// register them as field docs on the capitalized module alias.
    fn collect_module_field_docs(
        &mut self,
        alias_name: &SmolStr,
        declarations: &[TixDeclaration],
        prefix: &[SmolStr],
    ) {
        for decl in declarations {
            match decl {
                TixDeclaration::ValDecl { name, doc, .. } => {
                    if let Some(doc) = doc {
                        let mut path = prefix.to_vec();
                        path.push(name.clone());
                        self.docs
                            .insert_field_doc(alias_name.clone(), path, doc.clone());
                    }
                }
                TixDeclaration::Module {
                    name,
                    declarations: nested,
                    doc,
                } => {
                    if let Some(doc) = doc {
                        let mut path = prefix.to_vec();
                        path.push(name.clone());
                        self.docs
                            .insert_field_doc(alias_name.clone(), path, doc.clone());
                    }
                    let mut child_prefix = prefix.to_vec();
                    child_prefix.push(name.clone());
                    self.collect_module_field_docs(alias_name, nested, &child_prefix);
                }
                TixDeclaration::TypeAlias { .. } => {}
            }
        }
    }

    /// Look up a type alias by name.
    pub fn get(&self, name: &str) -> Option<&ParsedTy> {
        self.aliases.get(name)
    }

    /// Get the global val declarations map.
    pub fn global_vals(&self) -> &HashMap<SmolStr, ParsedTy> {
        &self.global_vals
    }

    /// Return the embedded source for a built-in context by name.
    ///
    /// Known contexts: `"nixos"`, `"home-manager"`.
    pub fn builtin_context_source(name: &str) -> Option<&'static str> {
        match name {
            "nixos" => Some(NIXOS_CONTEXT_STUBS),
            "home-manager" => Some(HM_CONTEXT_STUBS),
            _ => None,
        }
    }

    /// Parse a `.tix` source string as context stubs, loading any type aliases
    /// into `self.aliases` (so they can be referenced by val declarations) and
    /// returning the val declarations as a name→ParsedTy map.
    ///
    /// Unlike `load_tix_file`, val declarations are NOT added to `global_vals`
    /// — they represent lambda parameter types for a specific context, not
    /// globally available names.
    pub fn load_context_stubs(
        &mut self,
        source: &str,
    ) -> Result<HashMap<SmolStr, ParsedTy>, Box<dyn std::error::Error>> {
        let file = comment_parser::parse_tix_file(source)?;
        let mut context_args = HashMap::new();
        let mut target = ValTarget::ContextArgs(&mut context_args);
        self.load_declarations(&file.declarations, &mut target);
        self.load_field_docs(&file.field_docs);
        Ok(context_args)
    }

    /// Load context stubs for a named built-in context (e.g. "nixos").
    ///
    /// If `builtin_stubs_dir` is set, checks for `<dir>/<name>.tix` first.
    /// Falls back to the compiled-in minimal stubs if the file doesn't exist
    /// or the override dir isn't set.
    ///
    /// Returns `None` if the name doesn't match any known context.
    /// Returns `Some(Err(...))` if the source fails to parse.
    pub fn load_context_by_name(
        &mut self,
        name: &str,
    ) -> Option<Result<HashMap<SmolStr, ParsedTy>, Box<dyn std::error::Error>>> {
        // Check override directory first.
        if let Some(ref dir) = self.builtin_stubs_dir {
            let path = dir.join(format!("{name}.tix"));
            if path.is_file() {
                return Some(match std::fs::read_to_string(&path) {
                    Ok(source) => self.load_context_stubs(&source),
                    Err(e) => Err(format!("failed to read {}: {e}", path.display()).into()),
                });
            }
        }

        // Fall back to compiled-in stubs.
        let source = Self::builtin_context_source(name)?;
        Some(self.load_context_stubs(source))
    }

    /// Validate the registry for cycles in alias references.
    /// Returns `Err` with the names involved in cycles if any are found.
    pub fn validate(&self) -> Result<(), Vec<SmolStr>> {
        let mut cycles = Vec::new();
        let mut visited = HashMap::<SmolStr, VisitState>::new();

        for name in self.aliases.keys() {
            if self.has_cycle(name, &mut visited) {
                cycles.push(name.clone());
            }
        }

        if cycles.is_empty() {
            Ok(())
        } else {
            Err(cycles)
        }
    }

    /// DFS cycle detection for alias references.
    fn has_cycle(&self, name: &SmolStr, visited: &mut HashMap<SmolStr, VisitState>) -> bool {
        match visited.get(name) {
            Some(VisitState::InProgress) => return true,
            Some(VisitState::Done) => return false,
            None => {}
        }

        visited.insert(name.clone(), VisitState::InProgress);

        if let Some(body) = self.aliases.get(name) {
            let refs = collect_references(body);
            for ref_name in refs {
                if self.aliases.contains_key(ref_name.as_str())
                    && self.has_cycle(&ref_name, visited)
                {
                    return true;
                }
            }
        }

        visited.insert(name.clone(), VisitState::Done);
        false
    }
}

#[derive(Debug, Clone, Copy)]
enum VisitState {
    InProgress,
    Done,
}

/// Capitalize the first character of a string (e.g. "lib" -> "Lib").
fn capitalize(s: &str) -> SmolStr {
    let mut chars = s.chars();
    match chars.next() {
        None => SmolStr::default(),
        Some(first) => {
            let capitalized: String = first.to_uppercase().chain(chars).collect();
            SmolStr::from(capitalized)
        }
    }
}

/// Convert a module's declarations into an open attrset ParsedTy.
/// Val declarations become named fields; nested modules become nested attrset fields.
fn module_to_attrset(declarations: &[TixDeclaration]) -> ParsedTy {
    let mut fields = std::collections::BTreeMap::new();

    for decl in declarations {
        match decl {
            TixDeclaration::ValDecl { name, ty, .. } => {
                fields.insert(name.clone(), ParsedTyRef::from(ty.clone()));
            }
            TixDeclaration::Module {
                name,
                declarations: nested,
                ..
            } => {
                let nested_attrset = module_to_attrset(nested);
                fields.insert(name.clone(), ParsedTyRef::from(nested_attrset));
            }
            // Type aliases inside modules define types but don't add attrset fields.
            TixDeclaration::TypeAlias { .. } => {}
        }
    }

    ParsedTy::AttrSet(AttrSetTy {
        fields,
        dyn_ty: None,
        open: true,
    })
}

/// Recursively merge two parsed attrsets. For each field in `new`:
/// - If both old and new have a field and both are `AttrSet`, recurse (nested module merge).
/// - Otherwise, the new field overwrites (last-wins).
///
/// The result is open if either input is open. `dyn_ty` takes new if present, else keeps old.
fn merge_parsed_attrsets(
    old: &AttrSetTy<ParsedTyRef>,
    new: &AttrSetTy<ParsedTyRef>,
) -> AttrSetTy<ParsedTyRef> {
    let mut merged_fields = old.fields.clone();

    for (name, new_ref) in &new.fields {
        let merged_val = match merged_fields.get(name) {
            // Both sides are attrsets — recurse to merge nested modules.
            Some(existing_ref)
                if matches!(existing_ref.0.as_ref(), ParsedTy::AttrSet(_))
                    && matches!(new_ref.0.as_ref(), ParsedTy::AttrSet(_)) =>
            {
                let ParsedTy::AttrSet(existing_inner) = existing_ref.0.as_ref() else {
                    unreachable!()
                };
                let ParsedTy::AttrSet(new_inner) = new_ref.0.as_ref() else {
                    unreachable!()
                };
                ParsedTyRef::from(ParsedTy::AttrSet(merge_parsed_attrsets(
                    existing_inner,
                    new_inner,
                )))
            }
            // Otherwise, new overwrites old.
            _ => new_ref.clone(),
        };
        merged_fields.insert(name.clone(), merged_val);
    }

    AttrSetTy {
        fields: merged_fields,
        dyn_ty: new.dyn_ty.clone().or_else(|| old.dyn_ty.clone()),
        open: old.open || new.open,
    }
}

/// Collect all `TypeVarValue::Reference` names from a ParsedTy.
fn collect_references(ty: &ParsedTy) -> Vec<SmolStr> {
    let mut refs = Vec::new();
    collect_references_inner(ty, &mut refs);
    refs
}

fn collect_references_inner(ty: &ParsedTy, refs: &mut Vec<SmolStr>) {
    match ty {
        ParsedTy::TyVar(comment_parser::TypeVarValue::Reference(name)) => {
            refs.push(name.clone());
        }
        ParsedTy::TyVar(comment_parser::TypeVarValue::Generic(_)) => {}
        ParsedTy::Primitive(_) => {}
        ParsedTy::List(inner) => collect_references_inner(&inner.0, refs),
        ParsedTy::Lambda { param, body } => {
            collect_references_inner(&param.0, refs);
            collect_references_inner(&body.0, refs);
        }
        ParsedTy::AttrSet(attr) => {
            for v in attr.fields.values() {
                collect_references_inner(&v.0, refs);
            }
            if let Some(dyn_ty) = &attr.dyn_ty {
                collect_references_inner(&dyn_ty.0, refs);
            }
        }
        ParsedTy::Union(members) | ParsedTy::Intersection(members) => {
            for m in members {
                collect_references_inner(&m.0, refs);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use comment_parser::parse_tix_file;

    #[test]
    fn load_type_alias() {
        let file = parse_tix_file("type Derivation = { name: string };").expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.get("Derivation").is_some());
        assert!(registry.validate().is_ok());
    }

    #[test]
    fn load_val_decl() {
        let file = parse_tix_file("val mkDerivation :: { name: string, ... } -> { name: string };")
            .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.global_vals().get("mkDerivation").is_some());
    }

    #[test]
    fn module_becomes_alias() {
        let file = parse_tix_file(
            r#"
            module lib {
                val id :: a -> a;
                module strings {
                    val concatStringsSep :: string -> [string] -> string;
                }
            }
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // "Lib" alias should exist (capitalized from "lib")
        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        match lib_ty {
            ParsedTy::AttrSet(attr) => {
                assert!(attr.fields.contains_key("id"));
                assert!(attr.fields.contains_key("strings"));
                assert!(attr.open);
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn cycle_detection() {
        let file = parse_tix_file(
            r#"
            type A = B;
            type B = A;
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.validate().is_err());
    }

    #[test]
    fn no_false_cycle() {
        let file = parse_tix_file(
            r#"
            type Derivation = { name: string };
            type Nullable = a | null;
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.validate().is_ok());
    }

    #[test]
    fn builtin_context_source_known() {
        assert!(TypeAliasRegistry::builtin_context_source("nixos").is_some());
        assert!(TypeAliasRegistry::builtin_context_source("home-manager").is_some());
    }

    #[test]
    fn builtin_context_source_unknown() {
        assert!(TypeAliasRegistry::builtin_context_source("unknown-context").is_none());
    }

    #[test]
    fn load_context_stubs_returns_vals() {
        let mut registry = TypeAliasRegistry::with_builtins();
        let context_args = registry
            .load_context_stubs("val config :: { ... };\nval lib :: Lib;")
            .expect("parse error");

        // Val declarations should be in the returned map, NOT in global_vals.
        assert!(context_args.contains_key("config"));
        assert!(context_args.contains_key("lib"));
        assert!(!registry.global_vals().contains_key("config"));
        assert!(!registry.global_vals().contains_key("lib"));
    }

    #[test]
    fn load_context_by_name_nixos() {
        let mut registry = TypeAliasRegistry::with_builtins();
        let result = registry.load_context_by_name("nixos");
        assert!(result.is_some(), "nixos context should be known");
        let context_args = result.unwrap().expect("should parse");
        assert!(context_args.contains_key("config"));
        assert!(context_args.contains_key("lib"));
        assert!(context_args.contains_key("pkgs"));
    }

    #[test]
    fn load_context_by_name_unknown() {
        let mut registry = TypeAliasRegistry::new();
        assert!(registry.load_context_by_name("nonexistent").is_none());
    }

    // =========================================================================
    // DocIndex tests
    // =========================================================================

    #[test]
    fn doc_index_decl_doc() {
        let src = "## A configuration type.\ntype Config = { ... };";
        let file = parse_tix_file(src).expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert_eq!(
            registry.docs.decl_doc("Config").map(|s| s.as_str()),
            Some("A configuration type.")
        );
    }

    #[test]
    fn doc_index_val_doc() {
        let src = "## Build a derivation.\nval mkDrv :: { ... } -> { ... };";
        let file = parse_tix_file(src).expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert_eq!(
            registry.docs.decl_doc("mkDrv").map(|s| s.as_str()),
            Some("Build a derivation.")
        );
    }

    #[test]
    fn doc_index_field_doc() {
        let src = r#"
            type Config = {
                ## Whether to enable.
                enable: bool,
                ...
            };
        "#;
        let file = parse_tix_file(src).expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let path = vec![SmolStr::from("enable")];
        assert_eq!(
            registry.docs.field_doc("Config", &path).map(|s| s.as_str()),
            Some("Whether to enable.")
        );
    }

    #[test]
    fn doc_index_nested_field_doc() {
        let src = r#"
            type Config = {
                ## Services section.
                services: {
                    ## Enable SSH.
                    enable: bool,
                    ...
                },
                ...
            };
        "#;
        let file = parse_tix_file(src).expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let path = vec![SmolStr::from("services")];
        assert_eq!(
            registry.docs.field_doc("Config", &path).map(|s| s.as_str()),
            Some("Services section.")
        );

        let path = vec![SmolStr::from("services"), SmolStr::from("enable")];
        assert_eq!(
            registry.docs.field_doc("Config", &path).map(|s| s.as_str()),
            Some("Enable SSH.")
        );
    }

    #[test]
    fn doc_index_module_val_becomes_field_doc() {
        let src = r#"
            module lib {
                ## Identity function.
                val id :: a -> a;
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let path = vec![SmolStr::from("id")];
        assert_eq!(
            registry.docs.field_doc("Lib", &path).map(|s| s.as_str()),
            Some("Identity function.")
        );
    }

    // =========================================================================
    // Module merging tests
    // =========================================================================

    #[test]
    fn module_merge_across_files() {
        let file1 = parse_tix_file(
            r#"
            module lib {
                val id :: a -> a;
            }
            "#,
        )
        .expect("parse file1");
        let file2 = parse_tix_file(
            r#"
            module lib {
                val const :: a -> b -> a;
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        match lib_ty {
            ParsedTy::AttrSet(attr) => {
                assert!(attr.fields.contains_key("id"), "should keep field from first file");
                assert!(
                    attr.fields.contains_key("const"),
                    "should have field from second file"
                );
                assert!(attr.open);
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn module_merge_nested() {
        let file1 = parse_tix_file(
            r#"
            module lib {
                module strings {
                    val concatStringsSep :: string -> [string] -> string;
                }
            }
            "#,
        )
        .expect("parse file1");
        let file2 = parse_tix_file(
            r#"
            module lib {
                module strings {
                    val splitString :: string -> string -> [string];
                }
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        let ParsedTy::AttrSet(lib_attr) = lib_ty else {
            panic!("expected AttrSet, got: {lib_ty:?}")
        };

        let strings_ref = lib_attr.fields.get("strings").expect("strings field should exist");
        let ParsedTy::AttrSet(strings_attr) = strings_ref.0.as_ref() else {
            panic!("expected nested AttrSet for strings")
        };

        assert!(
            strings_attr.fields.contains_key("concatStringsSep"),
            "should keep field from first file"
        );
        assert!(
            strings_attr.fields.contains_key("splitString"),
            "should have field from second file"
        );
    }

    #[test]
    fn module_merge_field_override() {
        let file1 = parse_tix_file(
            r#"
            module lib {
                val id :: a -> a;
            }
            "#,
        )
        .expect("parse file1");
        let file2 = parse_tix_file(
            r#"
            module lib {
                val id :: int -> int;
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        let ParsedTy::AttrSet(attr) = lib_ty else {
            panic!("expected AttrSet")
        };

        // The second file's type should win (last-wins for non-attrset fields).
        let id_ref = attr.fields.get("id").expect("id field should exist");
        match id_ref.0.as_ref() {
            ParsedTy::Lambda { param, .. } => {
                assert!(
                    matches!(param.0.as_ref(), ParsedTy::Primitive(_)),
                    "second file's `int -> int` should overwrite first file's `a -> a`"
                );
            }
            other => panic!("expected Lambda for id, got: {other:?}"),
        }
    }

    #[test]
    fn module_merge_over_type_alias() {
        let file1 = parse_tix_file("type Lib = int;").expect("parse file1");
        let file2 = parse_tix_file(
            r#"
            module lib {
                val id :: a -> a;
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        // Module should overwrite the non-attrset alias entirely.
        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        assert!(
            matches!(lib_ty, ParsedTy::AttrSet(_)),
            "module should overwrite non-attrset alias, got: {lib_ty:?}"
        );
    }
}
