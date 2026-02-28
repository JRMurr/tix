// ==============================================================================
// Parallel Import Inference via Rayon
// ==============================================================================
//
// For files with many imports (e.g. nixpkgs all-packages.nix with 2076 imports),
// sequential inference through file_root_type is prohibitively slow. This module
// provides a two-phase parallel alternative:
//
// Phase 1 (Discovery): Sequential BFS walk of the import graph using the Salsa
// database for parsing and name resolution. Produces a set of PrecomputedFile
// bundles and a DAG of import edges.
//
// Phase 2 (Inference): Topological sort + rayon parallel inference. Files at the
// same topological level have no dependencies on each other and can be inferred
// concurrently. Each level's results feed into the next level as import_types.
//
// This path bypasses Salsa's file_root_type memoization — results are stored in
// a HashMap instead. The sequential Salsa path remains the primary path for
// incremental single-file updates.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use lang_ast::{AstDb, ExprId, Module, NameResolution, NixFile};
use lang_ty::OutputTy;
use rayon::prelude::*;

use crate::aliases::TypeAliasRegistry;
use crate::imports::{
    extract_return_type, resolve_directory_path, scan_callpackage_imports, scan_literal_imports,
    ImportError, ImportErrorKind,
};

// ==============================================================================
// PrecomputedFile — all Salsa query results for one file
// ==============================================================================

/// Everything needed to infer a file's types without the Salsa database.
/// All fields are owned and Send+Sync, so they can be sent to rayon tasks.
pub struct PrecomputedFile {
    pub path: PathBuf,
    pub nix_file: NixFile,
    pub module: Module,
    pub name_res: NameResolution,
    pub indices: lang_ast::ModuleIndices,
    pub grouped_defs: lang_ast::GroupedDefs,
    /// Regular imports: (apply_expr_id, target_path)
    pub import_edges: Vec<(ExprId, PathBuf)>,
    /// callPackage imports: (outer_apply_id, inner_apply_id, target_path)
    pub callpkg_edges: Vec<(ExprId, ExprId, PathBuf)>,
}

// ==============================================================================
// Phase 1: Discover import graph (sequential, needs DB)
// ==============================================================================

/// Walk the import graph breadth-first starting from a root file's imports.
/// For each discovered file, run Salsa queries (parse, lower, nameres, etc.)
/// and scan for further imports. Returns a map of precomputed file data and
/// any errors encountered.
///
/// The root file itself is NOT included in the result — only its imports
/// (and their transitive imports) are precomputed.
pub fn discover_import_graph(
    db: &dyn AstDb,
    root_module: &Module,
    root_name_res: &NameResolution,
    root_path: &Path,
    max_files: Option<usize>,
    deadline: Option<Instant>,
    cancel_flag: Option<&Arc<AtomicBool>>,
) -> (HashMap<PathBuf, PrecomputedFile>, Vec<ImportError>) {
    let base_dir = root_path.parent().unwrap_or(Path::new("/"));
    let mut result = HashMap::new();
    let mut errors = Vec::new();
    let mut visited = HashSet::new();
    let mut queue: VecDeque<PathBuf> = VecDeque::new();

    // Seed the queue with the root file's direct imports.
    let root_imports = scan_literal_imports(root_module, root_name_res, base_dir);
    let root_callpkgs = scan_callpackage_imports(root_module, base_dir);

    for (_expr_id, target_path) in &root_imports {
        let target_path = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());
        if let Some(resolved) = resolve_directory_path(target_path) {
            if visited.insert(resolved.clone()) {
                queue.push_back(resolved);
            }
        }
    }
    for (_outer, _inner, _path_lit, target_path) in &root_callpkgs {
        let target_path = target_path
            .canonicalize()
            .unwrap_or_else(|_| target_path.clone());
        if let Some(resolved) = resolve_directory_path(target_path) {
            if visited.insert(resolved.clone()) {
                queue.push_back(resolved);
            }
        }
    }

    // BFS: process each file, discover its imports, add to queue.
    while let Some(file_path) = queue.pop_front() {
        // Check limits.
        if max_files.is_some_and(|cap| result.len() >= cap) {
            log::warn!(
                "parallel import discovery: file cap ({}) reached",
                max_files.unwrap()
            );
            break;
        }
        if deadline.is_some_and(|d| Instant::now() > d) {
            log::warn!("parallel import discovery: deadline exceeded");
            break;
        }
        if cancel_flag.is_some_and(|f| f.load(Ordering::Relaxed)) {
            log::info!("parallel import discovery: cancelled");
            break;
        }

        // Load the file via Salsa.
        let Some(nix_file) = db.load_file(&file_path) else {
            // File not found — record error but continue discovering others.
            // The error expr is not meaningful here (it belongs to whichever
            // file referenced this path), but we need to report it somehow.
            errors.push(ImportError {
                kind: ImportErrorKind::FileNotFound(file_path),
                at_expr: ExprId::from_raw(0.into()),
            });
            continue;
        };

        // Run Salsa queries for this file.
        let module = lang_ast::module(db, nix_file);
        let name_res = lang_ast::name_resolution(db, nix_file);
        let indices = lang_ast::module_indices(db, nix_file);
        let grouped_defs = lang_ast::group_def(db, nix_file);

        // Scan for imports in this file.
        let file_base_dir = file_path.parent().unwrap_or(Path::new("/"));
        let literal_imports = scan_literal_imports(&module, &name_res, file_base_dir);
        let callpkg_imports = scan_callpackage_imports(&module, file_base_dir);

        // Resolve and canonicalize import edges.
        let mut import_edges = Vec::new();
        for (expr_id, target_path) in literal_imports {
            let target_path = target_path
                .canonicalize()
                .unwrap_or_else(|_| target_path.clone());
            if let Some(resolved) = resolve_directory_path(target_path) {
                import_edges.push((expr_id, resolved.clone()));
                if visited.insert(resolved.clone()) {
                    queue.push_back(resolved);
                }
            }
        }

        let mut callpkg_edges = Vec::new();
        for (outer_id, inner_id, _path_lit, target_path) in callpkg_imports {
            let target_path = target_path
                .canonicalize()
                .unwrap_or_else(|_| target_path.clone());
            if let Some(resolved) = resolve_directory_path(target_path) {
                callpkg_edges.push((outer_id, inner_id, resolved.clone()));
                if visited.insert(resolved.clone()) {
                    queue.push_back(resolved);
                }
            }
        }

        result.insert(
            file_path.clone(),
            PrecomputedFile {
                path: file_path,
                nix_file,
                module,
                name_res,
                indices,
                grouped_defs,
                import_edges,
                callpkg_edges,
            },
        );
    }

    (result, errors)
}

// ==============================================================================
// Phase 2: Parallel inference via rayon
// ==============================================================================

/// Infer all files in the import graph in parallel using rayon.
///
/// 1. Topologically sorts the DAG (cycles get OutputTy::TyVar(0)).
/// 2. For each topological level, uses rayon::par_iter to infer all files
///    at that level concurrently.
/// 3. Results from level N feed into level N+1 as import_types.
///
/// Returns a map from file path to root OutputTy for each file.
pub fn infer_import_graph_parallel(
    graph: &HashMap<PathBuf, PrecomputedFile>,
    aliases: Arc<TypeAliasRegistry>,
    per_file_deadline_secs: u64,
    cancel_flag: Option<Arc<AtomicBool>>,
) -> HashMap<PathBuf, OutputTy> {
    if graph.is_empty() {
        return HashMap::new();
    }

    let levels = topological_levels(graph);
    let mut results: HashMap<PathBuf, OutputTy> = HashMap::new();

    for (level_idx, level) in levels.iter().enumerate() {
        // Check cancellation between levels.
        if cancel_flag
            .as_ref()
            .is_some_and(|f| f.load(Ordering::Relaxed))
        {
            log::info!("parallel inference: cancelled at level {level_idx}");
            break;
        }

        log::info!(
            "parallel inference: level {level_idx} — {} files",
            level.len()
        );

        // Infer all files at this level in parallel.
        let level_results: Vec<(PathBuf, OutputTy)> = level
            .par_iter()
            .filter_map(|path| {
                let file = graph.get(path)?;

                // Build import_types for this file from already-resolved
                // dependencies (previous levels).
                let mut import_types = HashMap::new();
                for (expr_id, target_path) in &file.import_edges {
                    if let Some(ty) = results.get(target_path) {
                        import_types.insert(*expr_id, ty.clone());
                    }
                    // Missing import → stays unconstrained (generic import :: a -> b)
                }
                for (outer_id, inner_id, target_path) in &file.callpkg_edges {
                    if let Some(ty) = results.get(target_path) {
                        import_types.insert(*inner_id, ty.clone());
                        import_types.insert(*outer_id, extract_return_type(ty));
                    }
                }

                let deadline = Some(Instant::now() + Duration::from_secs(per_file_deadline_secs));
                let cancel = cancel_flag.clone();

                let check_result = crate::check_with_precomputed(
                    &file.module,
                    &file.name_res,
                    &file.indices,
                    file.grouped_defs.clone(),
                    &aliases,
                    import_types,
                    HashMap::new(), // no context args for imported files
                    deadline,
                    cancel,
                );

                let root_ty = check_result
                    .inference
                    .and_then(|inf| inf.expr_ty_map.get(file.module.entry_expr).cloned())
                    .unwrap_or(OutputTy::TyVar(0));

                Some((path.clone(), root_ty))
            })
            .collect();

        // Merge level results into the global results map.
        for (path, ty) in level_results {
            results.insert(path, ty);
        }
    }

    results
}

// ==============================================================================
// Topological sort
// ==============================================================================

/// Compute topological levels (Kahn's algorithm) over the import DAG.
/// Files with no dependencies are at level 0. Files that depend only on
/// level-0 files are at level 1, etc. Cycles are broken by excluding
/// back-edges — cyclic files end up at whatever level their non-cyclic
/// deps put them at, and their import_types for cyclic deps will be empty
/// (degrading to TyVar).
fn topological_levels(graph: &HashMap<PathBuf, PrecomputedFile>) -> Vec<Vec<PathBuf>> {
    // Build in-degree map. Only count edges to files IN the graph.
    let mut in_degree: HashMap<&PathBuf, usize> = HashMap::new();
    let mut dependents: HashMap<&PathBuf, Vec<&PathBuf>> = HashMap::new();

    for path in graph.keys() {
        in_degree.entry(path).or_insert(0);
    }

    for (path, file) in graph {
        let mut deps: HashSet<&PathBuf> = HashSet::new();
        for (_, target) in &file.import_edges {
            if graph.contains_key(target) {
                deps.insert(target);
            }
        }
        for (_, _, target) in &file.callpkg_edges {
            if graph.contains_key(target) {
                deps.insert(target);
            }
        }
        for dep in deps {
            *in_degree.entry(path).or_insert(0) += 1;
            dependents.entry(dep).or_default().push(path);
        }
    }

    let mut levels = Vec::new();
    let mut queue: Vec<&PathBuf> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(path, _)| *path)
        .collect();

    let mut remaining = graph.len();

    while !queue.is_empty() {
        let level: Vec<PathBuf> = queue.iter().map(|p| (*p).clone()).collect();
        let mut next_queue = Vec::new();

        for path in &queue {
            if let Some(deps) = dependents.get(path) {
                for dep in deps {
                    if let Some(deg) = in_degree.get_mut(dep) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            next_queue.push(*dep);
                        }
                    }
                }
            }
        }

        remaining -= level.len();
        levels.push(level);
        queue = next_queue;
    }

    // Any remaining files are in cycles — put them in a final level.
    if remaining > 0 {
        let cycle_files: Vec<PathBuf> = in_degree
            .iter()
            .filter(|(_, &deg)| deg > 0)
            .map(|(path, _)| (*path).clone())
            .collect();
        log::info!(
            "parallel inference: {} files in import cycles, degrading",
            cycle_files.len()
        );
        levels.push(cycle_files);
    }

    levels
}
