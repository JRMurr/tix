// ==============================================================================
// Type Alias Registry
// ==============================================================================
//
// Holds type aliases and global val declarations loaded from .tix stub files.
// `TypeAliasRegistry` is built before inference begins and passed into `CheckCtx`
// so that `TypeVarValue::Reference` names resolve against loaded aliases, and
// unresolved names can fall back to global val declarations.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use comment_parser::{ParsedTy, ParsedTyRef, SourceLocation, TixDeclFile, TixDeclaration};
use lang_ty::{AttrSetTy, TypeArena};
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
    ///
    /// When no doc exists at the exact path, falls back to searching for a
    /// longer path that ends with the same segments. This lets flat re-exports
    /// (e.g. `lib.findFirst`) inherit docs from their submodule source
    /// (e.g. `lib.lists.findFirst`) without duplicating doc comments.
    pub fn field_doc(&self, alias: &str, path: &[SmolStr]) -> Option<&SmolStr> {
        let entries = self.field_docs.get(alias)?;
        if let Some(doc) = entries.get(path) {
            return Some(doc);
        }
        // Fallback: find a longer path whose suffix matches `path`.
        // e.g. path=["findFirst"] matches stored ["lists", "findFirst"].
        entries
            .iter()
            .find(|(stored_path, _)| stored_path.len() > path.len() && stored_path.ends_with(path))
            .map(|(_, doc)| doc)
    }

    /// Number of aliases with field docs.
    pub fn field_docs_count(&self) -> usize {
        self.field_docs.values().map(|m| m.len()).sum()
    }

    /// Number of declaration-level docs.
    pub fn decl_docs_count(&self) -> usize {
        self.decl_docs.len()
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
// DeclLocation — source location of a declaration in a .tix stub file
// =============================================================================

/// Points to a declaration (type alias, module, or val) in a `.tix` stub file
/// on disk. Used by `textDocument/typeDefinition` and `textDocument/definition`
/// to navigate to stub declarations. When `source` is present, the LSP can
/// jump to the original source (e.g. in nixpkgs) instead of the `.tix` file.
#[derive(Debug, Clone)]
pub struct DeclLocation {
    pub file_path: PathBuf,
    pub span: (usize, usize),
    /// Original source location from `@source` annotation in the `.tix` file.
    /// When present with a matching source root, the LSP jumps here instead
    /// of to the `.tix` file.
    pub source: Option<SourceLocation>,
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

    /// Module stubs already loaded from `builtin_stubs_dir` (by alias name).
    /// Prevents re-reading and re-parsing large stubs (e.g. pkgs.tix) on
    /// every call to `load_context_by_name`.
    loaded_module_stubs: HashSet<SmolStr>,

    /// Cached context args from `load_context_by_name`. Avoids re-reading and
    /// re-parsing multi-MB context stubs (e.g. nixos.tix at 3.9MB) on every
    /// call when `tix check` processes many files with the same context.
    cached_context_args: HashMap<SmolStr, Arc<HashMap<SmolStr, ParsedTy>>>,

    /// Source locations for declarations (type aliases, modules, vals) loaded
    /// from disk-based `.tix` files. Multiple locations per name when it
    /// appears in several stub files. Populated by `load_tix_file_with_path`
    /// — compiled-in stubs (via `load_tix_file`) intentionally have no locations.
    decl_locations: HashMap<SmolStr, Vec<DeclLocation>>,

    /// Maps source identifiers to root paths for resolving `@source` annotations.
    /// e.g. `"nixpkgs"` → `/nix/store/...-source`, `"home-manager"` → `/nix/store/...-hm`.
    /// Set during stub generation/loading when the source roots are known.
    source_roots: HashMap<SmolStr, PathBuf>,
}

/// Shared, read-only map of context argument names to their declared types.
/// Wrapped in `Arc` so that cloning is a cheap refcount bump — important when
/// large context stubs (e.g. 24K+ val declarations from pkgs.tix) are shared
/// across many files during `tix check`.
pub type ContextArgs = Arc<HashMap<SmolStr, ParsedTy>>;

/// Controls where val declarations are routed during `load_declarations`.
enum ValTarget<'a> {
    /// Store in the registry's `global_vals` map (normal .tix file loading).
    GlobalVals,
    /// Collect into a separate map (context stub loading).
    ContextMap(&'a mut HashMap<SmolStr, ParsedTy>),
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
        // If the directory contains lib.tix, reload it with path tracking.
        // The type data is identical to what `with_builtins()` already loaded
        // (inserts overwrite), but now `DeclLocation` entries exist so
        // go-to-definition works for lib stubs like `lib.id`, `mkDerivation`, etc.
        let lib_path = dir.join("lib.tix");
        if lib_path.is_file() {
            match std::fs::read_to_string(&lib_path) {
                Ok(source) => match comment_parser::parse_tix_file(&source) {
                    Ok(file) => self.load_tix_file_with_path(&file, &lib_path),
                    Err(e) => log::warn!("Failed to parse {}: {e}", lib_path.display()),
                },
                Err(e) => log::warn!("Failed to read {}: {e}", lib_path.display()),
            }
        }

        self.builtin_stubs_dir = Some(dir);
    }

    /// Load declarations from a parsed .tix file into the registry.
    pub fn load_tix_file(&mut self, file: &TixDeclFile) {
        let mut target = ValTarget::GlobalVals;
        self.load_declarations(&file.declarations, &mut target);
        self.load_field_docs(&file.field_docs);
    }

    /// Load declarations from a parsed .tix file, recording source locations
    /// for type aliases and modules so `textDocument/typeDefinition` can
    /// navigate to them. Use this for stubs loaded from disk; compiled-in
    /// stubs should use `load_tix_file` (no path to record).
    pub fn load_tix_file_with_path(&mut self, file: &TixDeclFile, path: &Path) {
        self.load_tix_file(file);
        self.record_decl_locations(&file.declarations, path);
    }

    /// Walk declarations and record `DeclLocation` entries for each
    /// `TypeAlias`, `Module` (using the capitalized alias name), and `ValDecl`
    /// (keyed by the val's bare name). Pushes to existing entries so
    /// declarations spread across multiple files accumulate all their locations.
    fn record_decl_locations(&mut self, declarations: &[TixDeclaration], path: &Path) {
        for decl in declarations {
            match decl {
                TixDeclaration::TypeAlias {
                    name, span, source, ..
                } => {
                    self.decl_locations
                        .entry(name.clone())
                        .or_default()
                        .push(DeclLocation {
                            file_path: path.to_path_buf(),
                            span: *span,
                            source: source.clone(),
                        });
                }
                TixDeclaration::Module {
                    name,
                    declarations: nested,
                    span,
                    source,
                    ..
                } => {
                    // Modules generate a capitalized alias (e.g. "lib" -> "Lib").
                    let alias_name = capitalize(name);
                    self.decl_locations
                        .entry(alias_name)
                        .or_default()
                        .push(DeclLocation {
                            file_path: path.to_path_buf(),
                            span: *span,
                            source: source.clone(),
                        });
                    // Recurse into nested modules.
                    self.record_decl_locations(nested, path);
                }
                TixDeclaration::ValDecl {
                    name, span, source, ..
                } => {
                    self.decl_locations
                        .entry(name.clone())
                        .or_default()
                        .push(DeclLocation {
                            file_path: path.to_path_buf(),
                            span: *span,
                            source: source.clone(),
                        });
                }
            }
        }
    }

    /// Look up source locations for a declaration name in `.tix` files.
    /// Works for type aliases, module names, and val declarations.
    /// Returns an empty slice for compiled-in stubs and names not loaded from
    /// disk. Multiple entries when the name appears across several files.
    pub fn decl_locations(&self, name: &str) -> &[DeclLocation] {
        self.decl_locations
            .get(name)
            .map(|v| v.as_slice())
            .unwrap_or_default()
    }

    /// Register a source root for resolving `@source` annotations.
    /// e.g. `set_source_root("nixpkgs", "/nix/store/...-source")`.
    pub fn set_source_root(&mut self, id: impl Into<SmolStr>, root: PathBuf) {
        self.source_roots.insert(id.into(), root);
    }

    /// Source roots for resolving `@source` annotations in `DeclLocation`s.
    pub fn source_roots(&self) -> &HashMap<SmolStr, PathBuf> {
        &self.source_roots
    }

    /// Recursively load declarations. `val_target` controls where val
    /// declarations are routed: `GlobalVals` adds them to the registry's
    /// `global_vals` map; `ContextMap` collects them into a separate map
    /// for context-scoped parameters.
    fn load_declarations(
        &mut self,
        declarations: &[TixDeclaration],
        val_target: &mut ValTarget<'_>,
    ) {
        for decl in declarations {
            match decl {
                TixDeclaration::TypeAlias {
                    name, body, doc, ..
                } => {
                    self.aliases.insert(name.clone(), body.clone());
                    if let Some(doc) = doc {
                        self.docs.insert_decl_doc(name.clone(), doc.clone());
                    }
                }
                TixDeclaration::ValDecl { name, ty, doc, .. } => {
                    match val_target {
                        ValTarget::GlobalVals => {
                            self.global_vals.insert(name.clone(), ty.clone());
                        }
                        ValTarget::ContextMap(ref mut map) => {
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
                    ..
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

                    // Also register nested modules as top-level aliases so they
                    // can be referenced by val declarations (e.g. alias targets
                    // like `val python3Packages :: Python313Packages;` inside
                    // `module pkgs { ... }`).
                    self.register_nested_module_aliases(declarations);
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
                    ..
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

    /// Register nested module declarations as top-level type aliases.
    /// This enables references like `val python3Packages :: Python313Packages;`
    /// inside `module pkgs { ... }` where `python313Packages` is a nested module.
    fn register_nested_module_aliases(&mut self, declarations: &[TixDeclaration]) {
        for decl in declarations {
            if let TixDeclaration::Module {
                name,
                declarations: nested,
                ..
            } = decl
            {
                let alias_name = capitalize(name);
                // Only register if not already present — don't overwrite
                // explicitly declared top-level aliases.
                self.aliases
                    .entry(alias_name)
                    .or_insert_with(|| module_to_attrset(nested));
                // Recurse into deeper nesting.
                self.register_nested_module_aliases(nested);
            }
        }
    }

    /// Register a single inline type alias (from a doc comment in a .nix file).
    /// Inline aliases shadow any existing alias with the same name.
    pub fn load_inline_alias(&mut self, name: SmolStr, body: ParsedTy) {
        self.aliases.insert(name, body);
    }

    /// Look up a type alias by name.
    pub fn get(&self, name: &str) -> Option<&ParsedTy> {
        self.aliases.get(name)
    }

    /// Number of registered type aliases.
    pub fn alias_count(&self) -> usize {
        self.aliases.len()
    }

    /// Get the global val declarations map.
    pub fn global_vals(&self) -> &HashMap<SmolStr, ParsedTy> {
        &self.global_vals
    }

    /// Return the embedded source for a built-in context by name.
    ///
    /// Known contexts: `"nixos"`, `"home-manager"`.
    /// Note: `"callpackage"` (and other module-derived contexts) are handled
    /// by `load_context_by_name` via alias lookup, not by this function.
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
        let mut target = ValTarget::ContextMap(&mut context_args);
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
    ) -> Option<Result<ContextArgs, Box<dyn std::error::Error>>> {
        // Return cached result if available. Context stubs are immutable once
        // loaded, so the parsed args are safe to reuse across files.
        let cache_key = SmolStr::from(name);
        if let Some(cached) = self.cached_context_args.get(&cache_key) {
            return Some(Ok(Arc::clone(cached)));
        }

        // Check override directory first.
        if let Some(ref dir) = self.builtin_stubs_dir {
            let path = dir.join(format!("{name}.tix"));
            if path.is_file() {
                log::debug!("Loading context stubs for @{name} from {}", path.display());
                return Some(match std::fs::read_to_string(&path) {
                    Ok(source) => {
                        let result = self.load_context_stubs(&source);
                        match result {
                            Ok(args) => {
                                // Context files like nixos.tix declare `val pkgs :: Pkgs;`
                                // — the Pkgs alias may have a corresponding module stub
                                // (pkgs.tix) that needs loading to populate all fields.
                                self.preload_module_stubs_for_context_args(&args);
                                let arc = Arc::new(args);
                                self.cached_context_args.insert(cache_key, Arc::clone(&arc));
                                Ok(arc)
                            }
                            Err(e) => Err(e),
                        }
                    }
                    Err(e) => Err(format!("failed to read {}: {e}", path.display()).into()),
                });
            }
        }

        // Fall back to compiled-in stubs.
        if let Some(source) = Self::builtin_context_source(name) {
            let result = self.load_context_stubs(source);
            return Some(match result {
                Ok(args) => {
                    self.preload_module_stubs_for_context_args(&args);
                    let arc = Arc::new(args);
                    self.cached_context_args.insert(cache_key, Arc::clone(&arc));
                    Ok(arc)
                }
                Err(e) => Err(e),
            });
        }

        // Derive context from a module alias: @callpackage -> Pkgs, @lib -> Lib, etc.
        // If the corresponding alias exists as an attrset, extract its fields as
        // context args. This avoids duplicating module declarations in separate
        // context stub files — e.g. `module pkgs { ... }` in lib.tix already
        // defines all the fields that a callPackage-style file would need.
        //
        // Well-known aliases map context names to their canonical alias:
        //   "callpackage" -> "Pkgs" (callPackage-style files get the full package set)
        // For other names, capitalize: "foo" -> "Foo".
        let alias_name = match name {
            "callpackage" => SmolStr::from("Pkgs"),
            other => capitalize(other),
        };

        // If builtin_stubs_dir has a matching module stub, load it first
        // to ensure the alias is fully populated before extracting fields.
        // e.g. @callpackage → Pkgs → module pkgs → pkgs.tix
        self.try_load_module_stub(&alias_name);

        if let Some(ParsedTy::AttrSet(attr)) = self.aliases.get(&alias_name).cloned() {
            let mut context_args = HashMap::new();
            for (field_name, field_ty) in &attr.fields {
                context_args.insert(field_name.clone(), (*field_ty.0).clone());
            }
            // Also map the module name itself to the full alias type. In nixpkgs,
            // `pkgs.pkgs` is a self-reference, so files with `{ pkgs, ... }:`
            // should get `pkgs :: Pkgs` rather than an untyped `{..}`.
            let module_name = SmolStr::from(alias_name.to_ascii_lowercase());
            context_args.entry(module_name).or_insert_with(|| {
                ParsedTy::TyVar(comment_parser::TypeVarValue::Reference(alias_name.clone()))
            });
            let arc = Arc::new(context_args);
            self.cached_context_args.insert(cache_key, Arc::clone(&arc));
            return Some(Ok(arc));
        }

        None
    }

    /// Best-effort load of a module stub from `builtin_stubs_dir`.
    ///
    /// Given an alias name like `"Pkgs"`, looks for `pkgs.tix` in the stubs
    /// directory. If found and not already loaded, parses it and merges its
    /// declarations into the registry. This is a no-op when `builtin_stubs_dir`
    /// isn't set or the file doesn't exist.
    fn try_load_module_stub(&mut self, alias_name: &SmolStr) {
        if self.loaded_module_stubs.contains(alias_name) {
            return;
        }
        if let Some(ref dir) = self.builtin_stubs_dir {
            let module_name = alias_name.to_ascii_lowercase();
            let module_path = dir.join(format!("{module_name}.tix"));
            match std::fs::read_to_string(&module_path) {
                Ok(source) => match comment_parser::parse_tix_file(&source) {
                    Ok(file) => {
                        self.load_tix_file_with_path(&file, &module_path);
                        self.loaded_module_stubs.insert(alias_name.clone());
                    }
                    Err(e) => {
                        log::warn!("Failed to parse {}: {e}", module_path.display())
                    }
                },
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
                    log::warn!("Failed to read {}: {e}", module_path.display())
                }
                Err(_) => {} // File doesn't exist — not an error.
            }
        }
    }

    /// Scan context args for type alias references and preload their module
    /// stubs from `builtin_stubs_dir`.
    ///
    /// Context files like `nixos.tix` declare `val pkgs :: Pkgs;` — the `Pkgs`
    /// alias from `lib.tix` only has hand-curated entries, but `pkgs.tix` in
    /// the generated stubs directory has all ~24K nixpkgs attributes. Without
    /// this preloading, `pkgs.` completions only show the hand-curated subset.
    fn preload_module_stubs_for_context_args(&mut self, args: &HashMap<SmolStr, ParsedTy>) {
        // Collect references first to avoid borrow issues.
        let refs: Vec<SmolStr> = args
            .values()
            .filter_map(|ty| match ty {
                ParsedTy::TyVar(comment_parser::TypeVarValue::Reference(name)) => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();
        for alias_name in refs {
            self.try_load_module_stub(&alias_name);
        }
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
///
/// Each `val` declaration gets its own scope for generic type variables via
/// `rename_generics`. Without this, `a` in `val id :: a -> a` and `a` in
/// `val warn :: string -> a -> a` would share the same type variable when
/// the module is interned, causing constraints from one field to leak into
/// another.
fn module_to_attrset(declarations: &[TixDeclaration]) -> ParsedTy {
    let mut counter = 0usize;
    module_to_attrset_inner(declarations, &mut counter)
}

fn module_to_attrset_inner(declarations: &[TixDeclaration], counter: &mut usize) -> ParsedTy {
    let mut fields = std::collections::BTreeMap::new();

    for decl in declarations {
        match decl {
            TixDeclaration::ValDecl { name, ty, .. } => {
                // Each val declaration has its own scope for generic type
                // variables. Rename generics with a unique suffix so that
                // e.g. `a` in `val id :: a -> a` is independent from `a`
                // in `val warn :: string -> a -> a`.
                let scoped_ty = ty.rename_generics(&counter.to_string());
                *counter += 1;
                fields.insert(name.clone(), ParsedTyRef::from(scoped_ty));
            }
            TixDeclaration::Module {
                name,
                declarations: nested,
                ..
            } => {
                // Pass counter through so nested module vals also get unique
                // suffixes (avoids collisions between parent and child vals).
                let nested_attrset = module_to_attrset_inner(nested, counter);
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
        optional_fields: std::collections::BTreeSet::new(),
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
        optional_fields: old
            .optional_fields
            .union(&new.optional_fields)
            .cloned()
            .collect(),
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
        ParsedTy::Primitive(_) | ParsedTy::Top | ParsedTy::Bottom => {}
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
        // Type-level operators: opaque references have no type alias refs,
        // but Param/Return/FieldAccess may contain them in their inner types.
        ParsedTy::TypeOf(_) | ParsedTy::TypeOfImport(_) | ParsedTy::ImportType(_, _) => {}
        ParsedTy::Param(inner) | ParsedTy::Return(inner) => {
            collect_references_inner(&inner.0, refs);
        }
        ParsedTy::FieldAccess(inner, _) => {
            collect_references_inner(&inner.0, refs);
        }
    }
}

// ==============================================================================
// ParsedTy → OutputTy conversion
// ==============================================================================

/// Convert a `ParsedTy` to `OutputTy`, resolving type alias references through
/// a `TypeAliasRegistry`. Shared by CLI and LSP code paths.
///
/// `arena` is used to intern child `TyRef` nodes. All `TyRef` values in the
/// returned `OutputTy` are valid indices into the same arena.
///
/// `depth` guards against infinite recursion on self-referential aliases.
/// Generic type variables and unresolved references become `OutputTy::TyVar(0)`.
pub fn parsed_ty_to_output_ty(
    ty: &ParsedTy,
    registry: &TypeAliasRegistry,
    arena: &mut TypeArena,
    depth: usize,
) -> lang_ty::OutputTy {
    use comment_parser::TypeVarValue;
    use lang_ty::OutputTy;

    if depth > 20 {
        return OutputTy::TyVar(0);
    }

    match ty {
        ParsedTy::Primitive(p) => OutputTy::Primitive(*p),
        ParsedTy::TyVar(TypeVarValue::Reference(name)) => {
            if let Some(alias_body) = registry.get(name) {
                let inner = parsed_ty_to_output_ty(alias_body, registry, arena, depth + 1);
                let inner_ref = arena.intern(inner);
                OutputTy::Named(name.clone(), inner_ref)
            } else {
                OutputTy::TyVar(0)
            }
        }
        ParsedTy::TyVar(TypeVarValue::Generic(_)) => OutputTy::TyVar(0),
        ParsedTy::List(inner) => {
            let inner_ty = parsed_ty_to_output_ty(&inner.0, registry, arena, depth + 1);
            OutputTy::List(arena.intern(inner_ty))
        }
        ParsedTy::Lambda { param, body } => {
            let param_ty = parsed_ty_to_output_ty(&param.0, registry, arena, depth + 1);
            let body_ty = parsed_ty_to_output_ty(&body.0, registry, arena, depth + 1);
            OutputTy::Lambda {
                param: arena.intern(param_ty),
                body: arena.intern(body_ty),
            }
        }
        ParsedTy::AttrSet(attr) => {
            let fields = attr
                .fields
                .iter()
                .map(|(k, v)| {
                    let field_ty = parsed_ty_to_output_ty(&v.0, registry, arena, depth + 1);
                    (k.clone(), arena.intern(field_ty))
                })
                .collect();
            let dyn_ty = attr.dyn_ty.as_ref().map(|d| {
                let d_ty = parsed_ty_to_output_ty(&d.0, registry, arena, depth + 1);
                arena.intern(d_ty)
            });
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
                .map(|m| {
                    let m_ty = parsed_ty_to_output_ty(&m.0, registry, arena, depth + 1);
                    arena.intern(m_ty)
                })
                .collect(),
        ),
        ParsedTy::Intersection(members) => OutputTy::Intersection(
            members
                .iter()
                .map(|m| {
                    let m_ty = parsed_ty_to_output_ty(&m.0, registry, arena, depth + 1);
                    arena.intern(m_ty)
                })
                .collect(),
        ),
        ParsedTy::Top => OutputTy::Top,
        ParsedTy::Bottom => OutputTy::Bottom,
        // Type-level operators are not resolvable at the ParsedTy→OutputTy level
        // (they require inference context). Degrade to a fresh type variable.
        ParsedTy::TypeOf(_)
        | ParsedTy::TypeOfImport(_)
        | ParsedTy::ImportType(_, _)
        | ParsedTy::Param(_)
        | ParsedTy::Return(_)
        | ParsedTy::FieldAccess(_, _) => OutputTy::TyVar(0),
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
                assert!(
                    attr.fields.contains_key("id"),
                    "should keep field from first file"
                );
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

        let strings_ref = lib_attr
            .fields
            .get("strings")
            .expect("strings field should exist");
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

    #[test]
    fn module_merge_preserves_docs_from_both_files() {
        let file1 = parse_tix_file(
            r#"
            ## The standard library.
            module lib {
                ## Identity function.
                val id :: a -> a;
            }
            "#,
        )
        .expect("parse file1");
        let file2 = parse_tix_file(
            r#"
            module lib {
                ## Constant function.
                val const :: a -> b -> a;
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        // Types from both files should be present.
        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        let ParsedTy::AttrSet(attr) = lib_ty else {
            panic!("expected AttrSet, got: {lib_ty:?}")
        };
        assert!(attr.fields.contains_key("id"));
        assert!(attr.fields.contains_key("const"));

        // Docs from file1 should survive the merge.
        let id_path = vec![SmolStr::from("id")];
        assert_eq!(
            registry.docs.field_doc("Lib", &id_path).map(|s| s.as_str()),
            Some("Identity function."),
            "doc from first file should survive module merge"
        );

        // Docs from file2 should also be present.
        let const_path = vec![SmolStr::from("const")];
        assert_eq!(
            registry
                .docs
                .field_doc("Lib", &const_path)
                .map(|s| s.as_str()),
            Some("Constant function."),
            "doc from second file should be added"
        );

        // The decl doc for the module itself — file2 has no module-level doc,
        // so file1's doc should still be there.
        assert_eq!(
            registry.docs.decl_doc("Lib").map(|s| s.as_str()),
            Some("The standard library."),
            "module-level decl doc from first file should survive"
        );
    }

    #[test]
    fn module_merge_nested_preserves_docs() {
        let file1 = parse_tix_file(
            r#"
            module lib {
                module strings {
                    ## Join strings with a separator.
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
                    ## Split a string by delimiter.
                    val splitString :: string -> string -> [string];
                }
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        let concat_path = vec![SmolStr::from("strings"), SmolStr::from("concatStringsSep")];
        assert_eq!(
            registry
                .docs
                .field_doc("Lib", &concat_path)
                .map(|s| s.as_str()),
            Some("Join strings with a separator."),
            "nested doc from first file should survive merge"
        );

        let split_path = vec![SmolStr::from("strings"), SmolStr::from("splitString")];
        assert_eq!(
            registry
                .docs
                .field_doc("Lib", &split_path)
                .map(|s| s.as_str()),
            Some("Split a string by delimiter."),
            "nested doc from second file should be added"
        );
    }

    // =========================================================================
    // Context derivation from module aliases
    // =========================================================================

    #[test]
    fn load_context_by_name_callpackage() {
        // The built-in stubs define `module pkgs { ... }` which creates a `Pkgs` alias.
        // `@callpackage` should derive context args from that alias's fields.
        let mut registry = TypeAliasRegistry::with_builtins();
        let result = registry.load_context_by_name("callpackage");
        assert!(result.is_some(), "@callpackage context should be resolved");
        let context_args = result.unwrap().expect("should parse");
        assert!(
            context_args.contains_key("lib"),
            "Pkgs module should have a `lib` field"
        );
        assert!(
            context_args.contains_key("stdenv"),
            "Pkgs module should have a `stdenv` field"
        );
        assert!(
            context_args.contains_key("fetchurl"),
            "Pkgs module should have a `fetchurl` field"
        );
        assert!(
            context_args.contains_key("mkDerivation"),
            "Pkgs module should have a `mkDerivation` field"
        );
    }

    #[test]
    fn load_context_by_name_derives_from_module() {
        // Any module alias can be used as a context source: @foo -> Foo.
        let file = parse_tix_file(
            r#"
            module mycontext {
                val config :: { ... };
                val helper :: string -> int;
            }
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let result = registry.load_context_by_name("mycontext");
        assert!(
            result.is_some(),
            "@mycontext should resolve to Mycontext alias"
        );
        let context_args = result.unwrap().expect("should parse");
        assert!(context_args.contains_key("config"));
        assert!(context_args.contains_key("helper"));
    }

    #[test]
    fn load_context_by_name_non_attrset_alias_ignored() {
        // If the capitalized name exists but is NOT an attrset, don't use it.
        let file = parse_tix_file("type Foo = int;").expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(
            registry.load_context_by_name("foo").is_none(),
            "non-attrset alias should not be used as context"
        );
    }

    #[test]
    fn callpackage_context_loads_module_stub_from_builtin_stubs_dir() {
        // When builtin_stubs_dir contains pkgs.tix, @callpackage should
        // pick up packages defined there (not just the hand-curated builtins).
        let tmp =
            std::env::temp_dir().join(format!("tix_test_callpackage_stubs_{}", std::process::id()));
        let _ = std::fs::create_dir_all(&tmp);
        std::fs::write(
            tmp.join("pkgs.tix"),
            r#"
            type Derivation = { name: string, system: string, ... };
            module pkgs {
                val emilua :: Derivation;
                val gperf :: Derivation;
            }
            "#,
        )
        .expect("write pkgs.tix");

        let mut registry = TypeAliasRegistry::with_builtins();
        registry.set_builtin_stubs_dir(tmp.clone());

        let result = registry.load_context_by_name("callpackage");
        assert!(result.is_some(), "@callpackage should resolve via pkgs.tix");
        let context_args = result.unwrap().expect("should parse");

        assert!(
            context_args.contains_key("emilua"),
            "emilua should be in callpackage context"
        );
        assert!(
            context_args.contains_key("gperf"),
            "gperf should be in callpackage context"
        );

        // Verify the types are Derivation references, not bare type vars.
        match &context_args["emilua"] {
            ParsedTy::TyVar(comment_parser::TypeVarValue::Reference(name)) => {
                assert_eq!(name.as_str(), "Derivation");
            }
            other => panic!("expected Derivation reference, got: {other:?}"),
        }

        // Clean up.
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn context_file_preloads_referenced_module_stubs() {
        // When a context file (e.g. nixos.tix) declares `val pkgs :: Pkgs;`,
        // the module stub pkgs.tix should be loaded so that Pkgs has all fields.
        let tmp =
            std::env::temp_dir().join(format!("tix_test_context_preload_{}", std::process::id()));
        let _ = std::fs::create_dir_all(&tmp);

        // Write a context file that references Pkgs.
        std::fs::write(
            tmp.join("myctx.tix"),
            r#"
            val pkgs :: Pkgs;
            val lib :: Lib;
            "#,
        )
        .expect("write myctx.tix");

        // Write a pkgs module stub with extra packages.
        std::fs::write(
            tmp.join("pkgs.tix"),
            r#"
            module pkgs {
                val gh :: { name: string, ... };
                val ripgrep :: { name: string, ... };
            }
            "#,
        )
        .expect("write pkgs.tix");

        let mut registry = TypeAliasRegistry::with_builtins();
        registry.set_builtin_stubs_dir(tmp.clone());

        let result = registry.load_context_by_name("myctx");
        assert!(result.is_some(), "@myctx should resolve from file");
        let context_args = result.unwrap().expect("should parse");

        // pkgs should be typed as Pkgs.
        assert!(
            context_args.contains_key("pkgs"),
            "pkgs should be in context"
        );

        // Verify that the Pkgs alias now contains fields from pkgs.tix.
        match registry.aliases.get(&SmolStr::from("Pkgs")) {
            Some(ParsedTy::AttrSet(attr)) => {
                assert!(
                    attr.fields.contains_key("gh"),
                    "Pkgs alias should contain 'gh' from pkgs.tix, fields: {:?}",
                    attr.fields.keys().collect::<Vec<_>>()
                );
                assert!(
                    attr.fields.contains_key("ripgrep"),
                    "Pkgs alias should contain 'ripgrep' from pkgs.tix"
                );
            }
            other => panic!("expected Pkgs to be an AttrSet, got: {other:?}"),
        }

        let _ = std::fs::remove_dir_all(&tmp);
    }

    // =========================================================================
    // DeclLocation tracking tests
    // =========================================================================

    #[test]
    fn alias_location_tracked() {
        let stub = "type Derivation = { name: string };";
        let file = parse_tix_file(stub).expect("parse error");
        let path = std::path::PathBuf::from("/tmp/test_alias_loc.tix");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file_with_path(&file, &path);

        let locs = registry.decl_locations("Derivation");
        assert_eq!(locs.len(), 1, "should have exactly one location");
        assert_eq!(locs[0].file_path, path);
        assert_eq!(locs[0].span, (0, stub.len()));
    }

    #[test]
    fn module_alias_location_tracked() {
        let stub = "module lib { val id :: a -> a; }";
        let file = parse_tix_file(stub).expect("parse error");
        let path = std::path::PathBuf::from("/tmp/test_module_loc.tix");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file_with_path(&file, &path);

        // Module "lib" generates alias "Lib".
        let locs = registry.decl_locations("Lib");
        assert_eq!(locs.len(), 1, "module alias should have one location");
        assert_eq!(locs[0].file_path, path);
        assert_eq!(locs[0].span, (0, stub.len()));
    }

    #[test]
    fn builtin_stubs_have_no_location() {
        let registry = TypeAliasRegistry::with_builtins();
        // "Lib" is defined in the compiled-in stubs — no file path.
        assert!(
            registry.decl_locations("Lib").is_empty(),
            "compiled-in stubs should not have locations"
        );
    }

    #[test]
    fn load_tix_file_without_path_has_no_location() {
        let stub = "type Foo = int;";
        let file = parse_tix_file(stub).expect("parse error");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(
            registry.decl_locations("Foo").is_empty(),
            "load_tix_file should not record locations"
        );
    }

    #[test]
    fn multiple_stubs_accumulate_locations() {
        let stub_a = "module pkgs { val hello :: string; }";
        let stub_b = "module pkgs { val gcc :: string; }";
        let file_a = parse_tix_file(stub_a).expect("parse a");
        let file_b = parse_tix_file(stub_b).expect("parse b");
        let path_a = std::path::PathBuf::from("/tmp/a.tix");
        let path_b = std::path::PathBuf::from("/tmp/b.tix");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file_with_path(&file_a, &path_a);
        registry.load_tix_file_with_path(&file_b, &path_b);

        let locs = registry.decl_locations("Pkgs");
        assert_eq!(locs.len(), 2, "should accumulate locations from both stubs");
        assert_eq!(locs[0].file_path, path_a);
        assert_eq!(locs[1].file_path, path_b);
    }

    #[test]
    fn val_location_tracked() {
        let stub = "val mkDerivation :: { name: string } -> int;";
        let file = parse_tix_file(stub).expect("parse error");
        let path = std::path::PathBuf::from("/tmp/test_val_loc.tix");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file_with_path(&file, &path);

        let locs = registry.decl_locations("mkDerivation");
        assert_eq!(locs.len(), 1, "val declaration should have one location");
        assert_eq!(locs[0].file_path, path);
        assert_eq!(locs[0].span, (0, stub.len()));
    }

    #[test]
    fn module_nested_val_location_tracked() {
        let stub = "module lib { val id :: a -> a; }";
        let file = parse_tix_file(stub).expect("parse error");
        let path = std::path::PathBuf::from("/tmp/test_nested_val_loc.tix");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file_with_path(&file, &path);

        // The nested val "id" should be tracked.
        let locs = registry.decl_locations("id");
        assert_eq!(locs.len(), 1, "nested val should have one location");
        assert_eq!(locs[0].file_path, path);
    }

    #[test]
    fn builtin_stubs_dir_loads_lib() {
        // When builtin_stubs_dir contains lib.tix, set_builtin_stubs_dir
        // should reload it with path tracking so go-to-def works.
        let tmp = std::env::temp_dir().join("tix_test_builtin_stubs_dir_loads_lib");
        let _ = std::fs::create_dir_all(&tmp);

        // Write a minimal lib.tix that mirrors the compiled-in stubs' structure.
        let lib_stub = "module lib { val id :: a -> a; }";
        std::fs::write(tmp.join("lib.tix"), lib_stub).expect("write lib.tix");

        let mut registry = TypeAliasRegistry::with_builtins();

        // Before setting the dir, compiled-in stubs have no locations.
        assert!(
            registry.decl_locations("Lib").is_empty(),
            "compiled-in stubs should not have locations before set_builtin_stubs_dir"
        );

        registry.set_builtin_stubs_dir(tmp.clone());

        // After setting the dir, lib.tix should be reloaded with path tracking.
        let lib_path = tmp.join("lib.tix");
        let locs = registry.decl_locations("Lib");
        assert!(
            !locs.is_empty(),
            "Lib should have locations after set_builtin_stubs_dir"
        );
        assert_eq!(locs[0].file_path, lib_path);

        // Val declarations inside the module should also be tracked.
        let id_locs = registry.decl_locations("id");
        assert!(
            !id_locs.is_empty(),
            "nested val 'id' should have locations after set_builtin_stubs_dir"
        );
        assert_eq!(id_locs[0].file_path, lib_path);

        // Clean up.
        let _ = std::fs::remove_dir_all(&tmp);
    }
}
