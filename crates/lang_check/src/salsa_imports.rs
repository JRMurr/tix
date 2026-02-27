// ==============================================================================
// Salsa-tracked import inference
// ==============================================================================
//
// Replaces the manual `import_cache: HashMap<PathBuf, OutputTy>` with Salsa's
// automatic memoization and invalidation. `file_root_type(db, file)` is a
// tracked function: Salsa caches the result and re-runs only when the file's
// contents (or its transitive imports' contents) change.
//
// Benefits over the manual cache:
// - Automatic invalidation: editing a deep dependency re-infers only affected files
// - No manual cache.remove() needed
// - Cycle detection via Salsa's built-in cycle recovery
// - Thread safety without external locking

use std::collections::HashMap;
use std::path::Path;
use std::time::{Duration, Instant};

use lang_ast::{AstDb, ExprId, Module, NameResolution, NixFile, StubConfig};
use lang_ty::OutputTy;

use crate::aliases::TypeAliasRegistry;
use crate::imports::{
    extract_return_type, resolve_directory_path, scan_callpackage_imports, scan_literal_imports,
};

// ==============================================================================
// TypeAliasRegistry builder (from StubConfig)
// ==============================================================================

/// Build a TypeAliasRegistry from the Salsa-managed StubConfig.
///
/// Not a Salsa tracked function because TypeAliasRegistry doesn't implement
/// the required `salsa::Update` trait. Instead, this is a plain helper called
/// from `file_root_type`. Since `file_root_type` itself is Salsa-tracked and
/// reads StubConfig fields (which Salsa tracks), the registry is effectively
/// cached: when StubConfig hasn't changed, file_root_type returns its cached
/// result without rebuilding the registry.
pub fn build_type_alias_registry(db: &dyn AstDb, config: StubConfig) -> TypeAliasRegistry {
    let mut registry = if config.use_builtins(db) {
        TypeAliasRegistry::with_builtins()
    } else {
        TypeAliasRegistry::new()
    };

    if let Some(dir) = config.builtin_stubs_dir(db) {
        registry.set_builtin_stubs_dir(dir.clone());
    }

    for path in config.stub_paths(db) {
        if let Err(e) = load_stubs_recursive(&mut registry, path) {
            log::warn!("Failed to load stubs from {}: {e}", path.display());
        }
    }

    if let Err(cycles) = registry.validate() {
        log::warn!("Cyclic type aliases detected: {:?}", cycles);
    }

    registry
}

/// Load .tix files from a path into the registry. Mirrors the CLI's
/// `load_stubs` function but lives here to avoid a dependency on the CLI crate.
fn load_stubs_recursive(
    registry: &mut TypeAliasRegistry,
    path: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                load_stubs_recursive(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                load_single_stub(registry, &entry_path)?;
            }
        }
    } else {
        load_single_stub(registry, path)?;
    }
    Ok(())
}

fn load_single_stub(
    registry: &mut TypeAliasRegistry,
    path: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let source = std::fs::read_to_string(path)?;
    let file = comment_parser::parse_tix_file(&source)
        .map_err(|e| format!("Error parsing {}: {}", path.display(), e))?;
    registry.load_tix_file(&file);
    Ok(())
}

// ==============================================================================
// file_root_type (Salsa-tracked)
// ==============================================================================

/// Infer a file and return its root expression type. Salsa handles memoization
/// and cycle detection.
///
/// Replaces the manual `import_cache: HashMap<PathBuf, OutputTy>` — when a
/// file's contents change (via `set_file_contents`), Salsa automatically
/// invalidates this query and all queries that depend on it.
///
/// Uses `cycle_initial` for Salsa's fixpoint iteration on cyclic imports:
/// cyclic imports start with `OutputTy::TyVar(0)` (unconstrained), matching
/// the previous behavior of `resolve_imports`.
#[salsa::tracked(cycle_initial = file_root_type_initial)]
pub fn file_root_type(db: &dyn AstDb, file: NixFile) -> OutputTy {
    let module = lang_ast::module(db, file);
    let name_res = lang_ast::name_resolution(db, file);
    let grouped = lang_ast::group_def(db, file);
    let indices = lang_ast::module_indices(db, file);

    // Build the registry from the Salsa-managed StubConfig (if configured).
    // Falls back to a default registry when StubConfig hasn't been set
    // (e.g. in tests or CLI without --stubs).
    let aliases = match db.stub_config() {
        Some(config) => build_type_alias_registry(db, config),
        None => TypeAliasRegistry::default(),
    };

    // Load inline type aliases from doc comments (per-file).
    let mut aliases = aliases.clone();
    for alias_source in &module.inline_type_aliases {
        if let Some((name, body)) = comment_parser::parse_inline_type_alias(alias_source) {
            aliases.load_inline_alias(name, body);
        }
    }

    // Resolve imports via recursive Salsa calls.
    let import_types = resolve_import_types_salsa(db, &module, &name_res, file);

    // Run inference with a per-file deadline to prevent unbounded inference.
    let check = crate::CheckCtx::new(
        &module,
        &name_res,
        &indices.binding_expr,
        aliases,
        import_types,
        HashMap::new(),
    )
    .with_deadline(Instant::now() + Duration::from_secs(5));

    let (result, _, _) = check.infer_prog_partial(grouped);

    result
        .expr_ty_map
        .get(module.entry_expr)
        .cloned()
        .unwrap_or(OutputTy::TyVar(0))
}

/// Cycle initial value: unconstrained type variable.
/// When Salsa detects a cycle in file_root_type, the cycle head starts
/// with this value. Salsa iterates until the value converges.
fn file_root_type_initial(_db: &dyn AstDb, _id: salsa::Id, _file: NixFile) -> OutputTy {
    OutputTy::TyVar(0)
}

// ==============================================================================
// Import type resolution (using Salsa-memoized file_root_type)
// ==============================================================================

/// Scan a module for import expressions and resolve each target's root type
/// via the Salsa-memoized `file_root_type`. Returns the ExprId→OutputTy map
/// that `CheckCtx` needs for import-aware inference.
///
/// This replaces the manual recursive walk in `resolve_imports()` for the
/// type resolution portion. Navigation targets and error collection still
/// use the existing `resolve_imports()` in the LSP path.
///
/// Each `file_root_type` call may recurse back into this function for the
/// target's own imports, creating a call chain as deep as the import graph.
/// `stacker::maybe_grow` ensures we don't overflow the thread stack on deep
/// or wide import trees (same pattern as rustc and rust-analyzer).
fn resolve_import_types_salsa(
    db: &dyn AstDb,
    module: &Module,
    name_res: &NameResolution,
    file: NixFile,
) -> HashMap<ExprId, OutputTy> {
    let file_path = file.path(db);
    let base_dir = file_path.parent().unwrap_or(Path::new("/"));
    let mut types = HashMap::new();

    // Regular imports: `import ./path.nix`
    let literal_imports = scan_literal_imports(module, name_res, base_dir);
    for (apply_expr_id, target_path) in literal_imports {
        let target_path = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());
        let Some(target_path) = resolve_directory_path(target_path) else {
            continue;
        };

        let Some(target_file) = db.load_file(&target_path) else {
            continue;
        };

        // Grow the stack before recursing into file_root_type. Each recursive
        // call allocates Module, NameResolution, CheckCtx, etc. on the stack.
        // 256KB red zone, 1MB new segment when exceeded.
        let root_ty =
            stacker::maybe_grow(256 * 1024, 1024 * 1024, || file_root_type(db, target_file));
        types.insert(apply_expr_id, root_ty);
    }

    // callPackage imports: `callPackage ./path.nix {}`
    let callpackage_imports = scan_callpackage_imports(module, base_dir);
    for (outer_apply_id, inner_apply_id, _path_literal_id, target_path) in callpackage_imports {
        let target_path = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());
        let Some(target_path) = resolve_directory_path(target_path) else {
            continue;
        };

        let Some(target_file) = db.load_file(&target_path) else {
            continue;
        };

        let root_ty =
            stacker::maybe_grow(256 * 1024, 1024 * 1024, || file_root_type(db, target_file));
        types.insert(inner_apply_id, root_ty.clone());
        types.insert(outer_apply_id, extract_return_type(&root_ty));
    }

    types
}
