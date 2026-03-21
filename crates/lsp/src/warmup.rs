// ==============================================================================
// Batch Parallel Warmup for LSP Background Analysis
// ==============================================================================
//
// Replaces the one-at-a-time background queue with a batch parallel warmup
// that reuses the same layered approach as `tix check`. The pipeline:
//
//   Phase 1 (Sequential)  — Parse/lower/nameres all files via an independent
//                           Salsa database. Scan imports for the dependency
//                           graph. Build SyntaxBundles.
//   Phase 1.5             — build_file_layers() for topological ordering.
//   Phase 2 (Parallel)    — Layer-by-layer parallel inference via rayon.
//                           Each layer's dependencies are guaranteed cached.
//                           No eviction — the LSP needs all signatures.
//
// The warmup runs on spawn_blocking, so the async analysis loop stays
// responsive to user edits during warmup.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use lang_ast::{module_and_source_maps, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::coordinator::InferenceCoordinator;
use lang_check::diagnostic::TixDiagnostic;
use lang_check::imports::import_errors_to_diagnostics;
use rayon::prelude::*;
use smol_str::SmolStr;

use crate::convert::LineIndex;
use crate::project_config::ProjectConfig;
use crate::state::{FileSnapshot, InferenceData, SyntaxData};

/// Result of batch warmup for a single file. The caller (analysis loop) uses
/// these to populate state.files, DashMap snapshots, and publish diagnostics.
pub struct WarmupFileResult {
    pub path: PathBuf,
    pub syntax_data: SyntaxData,
    pub inference_data: InferenceData,
    pub file_analysis: crate::state::FileAnalysis,
    pub diagnostics: Vec<TixDiagnostic>,
    pub import_paths: Vec<PathBuf>,
}

/// Run batch warmup for a set of files using layered parallel inference.
///
/// Uses an independent Salsa database (no contention with the main LSP DB).
/// Results are returned for the caller to merge into LSP state.
///
/// `coordinator` is the shared LSP coordinator — signatures are cached directly
/// so handlers can resolve imports immediately.
pub fn run_batch_warmup(
    files: Vec<(PathBuf, String)>,
    registry: Arc<TypeAliasRegistry>,
    coordinator: &InferenceCoordinator,
    project_config: Option<&ProjectConfig>,
    config_dir: Option<&Path>,
    rss_limit_mb: Option<f64>,
) -> Vec<WarmupFileResult> {
    if files.is_empty() {
        return vec![];
    }

    let t_total = Instant::now();
    let file_count = files.len();
    log::info!("batch warmup: starting {} files", file_count);

    // =========================================================================
    // Phase 1 — Sequential Prepare
    // =========================================================================
    //
    // Uses its own RootDatabase (no contention with the main LSP Salsa DB).
    // Parses, lowers, does nameres, scans imports, builds SyntaxBundles.

    let db = RootDatabase::default();

    struct PreparedFile {
        path: PathBuf,
        parsed: rnix::Parse<rnix::Root>,
        nix_file: lang_ast::NixFile,
        module: lang_ast::Module,
        module_indices: lang_ast::ModuleIndices,
        source_map: lang_ast::ModuleSourceMap,
        name_res: lang_ast::NameResolution,
        scopes: lang_ast::ModuleScopes,
        grouped_defs: lang_ast::GroupedDefs,
        line_index: LineIndex,
        context_args: Arc<HashMap<SmolStr, comment_parser::ParsedTy>>,
        context_arg_types: HashMap<SmolStr, lang_ty::OutputTy>,
        context_arg_arena: Arc<lang_ty::TypeArena>,
        import_targets_raw: Vec<PathBuf>,
    }

    // We need a mutable clone of the registry for context resolution (which
    // may lazily load context stubs). The Arc is cloned, then we get a mutable
    // reference via Arc::make_mut.
    let mut registry_mut = (*registry).clone();

    let mut prepared: Vec<PreparedFile> = Vec::with_capacity(files.len());

    for (file_path, source_text) in &files {
        // Canonicalize so the path matches what scan_all_import_paths produces.
        // Without this, symlinked dirs (e.g. /tmp → /nix/store) would cause
        // import edges to not match file map keys.
        let file_path = &std::fs::canonicalize(file_path).unwrap_or_else(|_| file_path.clone());

        let nix_file = match db.read_file(file_path.clone()) {
            Ok(f) => f,
            Err(e) => {
                log::warn!("warmup: could not load {}: {e}", file_path.display());
                continue;
            }
        };

        let parsed = rnix::Root::parse(source_text);
        let (module, source_map) = module_and_source_maps(&db, nix_file);
        let module_indices = lang_ast::module_indices(&db, nix_file);
        let name_res = lang_ast::name_resolution(&db, nix_file);
        let scopes = lang_ast::scopes(&db, nix_file);
        let grouped_defs = lang_ast::group_def(&db, nix_file);
        let line_index = LineIndex::new(source_text);

        // Scan imports for dependency graph.
        let base_dir = file_path.parent().unwrap_or(Path::new("/"));
        let import_targets_raw =
            lang_check::imports::scan_all_import_paths(&module, &name_res, base_dir);

        // Resolve context args from tix.toml.
        let context_args: Arc<HashMap<SmolStr, comment_parser::ParsedTy>> =
            if let (Some(cfg), Some(dir)) = (project_config, config_dir) {
                crate::project_config::resolve_context_for_file(
                    file_path,
                    cfg,
                    dir,
                    &mut registry_mut,
                )
                .unwrap_or_else(|e| {
                    log::warn!(
                        "warmup: failed to resolve context for {}: {e}",
                        file_path.display()
                    );
                    Arc::default()
                })
            } else {
                Arc::default()
            };

        let (context_arg_types, context_arg_arena) =
            crate::ty_nav::convert_context_args(&context_args, &registry_mut);

        prepared.push(PreparedFile {
            path: file_path.clone(),
            parsed,
            nix_file,
            module,
            module_indices,
            source_map,
            name_res,
            scopes,
            grouped_defs,
            line_index,
            context_args,
            context_arg_types,
            context_arg_arena,
            import_targets_raw,
        });
    }

    // Wrap registry in Arc now that all context resolution mutations are done.
    let registry = Arc::new(registry_mut);

    let t_prepare = t_total.elapsed();
    log::info!(
        "batch warmup: Phase 1 prepared {} files in {:.1}ms",
        prepared.len(),
        t_prepare.as_secs_f64() * 1000.0,
    );

    // =========================================================================
    // Phase 1.5 — Dependency graph + topological layers
    // =========================================================================

    let mut import_edges: HashMap<PathBuf, Vec<PathBuf>> = HashMap::with_capacity(prepared.len());
    for pp in &prepared {
        import_edges.insert(pp.path.clone(), pp.import_targets_raw.clone());
    }

    let layers = lang_check::file_graph::build_file_layers(&import_edges);
    log::info!(
        "batch warmup: {} layers from {} files",
        layers.len(),
        prepared.len(),
    );

    // Build a lookup from path → PreparedFile for O(1) access during
    // parallel inference.
    let prepared_map: dashmap::DashMap<PathBuf, PreparedFile> =
        dashmap::DashMap::with_capacity(prepared.len());
    for pp in prepared {
        prepared_map.insert(pp.path.clone(), pp);
    }

    // =========================================================================
    // Phase 2 — Layered Parallel Inference
    // =========================================================================
    //
    // For each layer, infer files in parallel. Dependencies from prior layers
    // are in the coordinator cache. No eviction — the LSP needs all signatures
    // to stay cached for interactive use.

    let mut all_results: Vec<WarmupFileResult> = Vec::with_capacity(file_count);

    // Shared inference logic for a single file.
    let infer_one = |path: &PathBuf| -> Option<WarmupFileResult> {
        let (_, pp) = prepared_map.remove(path)?;

        // Resolve imports from coordinator cache. Prior layers' signatures
        // are available; intra-SCC imports within the same layer get ⊤.
        let base_dir = pp.path.parent().unwrap_or(Path::new("/"));
        let import_resolution = coordinator.resolve_imports(&pp.module, &pp.name_res, base_dir);
        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        let import_targets = import_resolution.targets;

        let file_dir = pp.path.parent().map(|p| p.to_path_buf());
        let name_to_import = crate::state::build_name_to_import(
            &pp.module,
            &import_targets,
            &pp.grouped_defs,
            file_dir.as_deref(),
        );

        // Build InferenceInputs and run inference.
        let inputs = lang_check::InferenceInputs {
            module: pp.module.clone(),
            module_indices: pp.module_indices.clone(),
            name_res: pp.name_res.clone(),
            grouped_defs: pp.grouped_defs.clone(),
            registry: Arc::clone(&registry),
            import_types: import_resolution.types,
            import_diagnostics,
            context_args: pp.context_args.clone(),
            rss_limit_mb,
            file_path: Some(pp.path.clone()),
        };

        let check_result = lang_check::run_inference(&inputs);

        // Cache this file's signature for subsequent layers.
        if let Some(sig) = lang_check::extract_file_signature(&check_result, pp.module.entry_expr) {
            coordinator.set_signature(&pp.path, sig);
        }

        let diagnostics = check_result.diagnostics.clone();

        let import_paths: Vec<PathBuf> = import_targets.values().cloned().collect();

        // Build LSP data structures. SyntaxData is built first by moving
        // fields out of pp; FileAnalysis clones from it to avoid redundant
        // copies from pp.
        let syntax_data = SyntaxData {
            parsed: pp.parsed,
            line_index: pp.line_index,
            module: pp.module,
            module_indices: pp.module_indices,
            source_map: pp.source_map,
            name_res: pp.name_res,
            scopes: pp.scopes,
            import_targets,
            name_to_import,
            context_arg_types: pp.context_arg_types,
            context_arg_arena: pp.context_arg_arena,
        };

        let inference_data = InferenceData {
            check_result: check_result.clone(),
        };

        let file_analysis = crate::state::FileAnalysis {
            nix_file: pp.nix_file,
            line_index: syntax_data.line_index.clone(),
            parsed: syntax_data.parsed.clone(),
            module: syntax_data.module.clone(),
            module_indices: syntax_data.module_indices.clone(),
            source_map: syntax_data.source_map.clone(),
            name_res: syntax_data.name_res.clone(),
            scopes: syntax_data.scopes.clone(),
            check_result,
            import_targets: syntax_data.import_targets.clone(),
            name_to_import: syntax_data.name_to_import.clone(),
            context_arg_types: syntax_data.context_arg_types.clone(),
            context_arg_arena: Arc::clone(&syntax_data.context_arg_arena),
        };

        Some(WarmupFileResult {
            path: pp.path,
            syntax_data,
            inference_data,
            file_analysis,
            diagnostics,
            import_paths,
        })
    };

    for (layer_idx, layer) in layers.iter().enumerate() {
        log::debug!(
            "batch warmup: layer {}/{} — {} files",
            layer_idx + 1,
            layers.len(),
            layer.len(),
        );

        // Check RSS before each layer. If memory pressure is high, stop
        // early to avoid OOM — the remaining files just won't have types.
        if let Some(limit) = rss_limit_mb {
            let rss = lang_check::rss_mb();
            if rss > limit {
                let remaining: usize = layers[layer_idx..].iter().map(|l| l.len()).sum();
                log::warn!(
                    "batch warmup: stopping at layer {} — RSS {:.0}MB > {:.0}MB limit, \
                     skipping {} remaining files",
                    layer_idx,
                    rss,
                    limit,
                    remaining,
                );
                break;
            }
        }

        let results: Vec<WarmupFileResult> = layer.par_iter().filter_map(&infer_one).collect();
        all_results.extend(results);
    }

    let elapsed = t_total.elapsed();
    log::info!(
        "batch warmup: completed {} / {} files in {:.1}ms ({} layers)",
        all_results.len(),
        file_count,
        elapsed.as_secs_f64() * 1000.0,
        layers.len(),
    );

    all_results
}

/// Convert warmup results into FileSnapshots for direct DashMap insertion.
impl WarmupFileResult {
    pub fn to_snapshot(&self) -> FileSnapshot {
        FileSnapshot {
            syntax: self.syntax_data.clone(),
            inference: Some(self.inference_data.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_check::coordinator::InferenceCoordinator;
    use std::io::Write;
    use tempfile::TempDir;

    /// Helper: write files to a temp dir and return (path, contents) pairs.
    fn write_nix_files(dir: &Path, files: &[(&str, &str)]) -> Vec<(PathBuf, String)> {
        files
            .iter()
            .map(|(name, contents)| {
                let path = dir.join(name);
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent).unwrap();
                }
                let mut f = std::fs::File::create(&path).unwrap();
                f.write_all(contents.as_bytes()).unwrap();
                (path, contents.to_string())
            })
            .collect()
    }

    #[test]
    fn warmup_independent_files() {
        // Three independent files with no imports. All should end up in one
        // layer and the coordinator should have signatures for each.
        let dir = TempDir::new().unwrap();
        let files = write_nix_files(
            dir.path(),
            &[("a.nix", "42"), ("b.nix", "\"hello\""), ("c.nix", "true")],
        );

        let registry = Arc::new(TypeAliasRegistry::with_builtins());
        let coordinator = InferenceCoordinator::new();

        let results = run_batch_warmup(files.clone(), registry, &coordinator, None, None, None);

        assert_eq!(results.len(), 3, "should get results for all 3 files");

        // Verify coordinator has signatures for all files.
        for (path, _) in &files {
            assert!(
                coordinator.get_signature(path).is_some(),
                "coordinator should have signature for {}",
                path.display()
            );
        }

        // Verify each result has inference data.
        for result in &results {
            assert!(
                result.inference_data.check_result.inference.is_some(),
                "file {} should have inference result",
                result.path.display()
            );
        }
    }

    #[test]
    fn warmup_with_imports() {
        // a.nix imports b.nix. The layered approach should infer b.nix first
        // (layer 0), then a.nix (layer 1) gets the real type from b.nix via
        // the coordinator. Verify the coordinator has both signatures and b.nix
        // is inferred before a.nix (b is in a lower layer).
        let dir = TempDir::new().unwrap();
        let files = write_nix_files(dir.path(), &[("a.nix", "import ./b.nix"), ("b.nix", "42")]);

        let registry = Arc::new(TypeAliasRegistry::with_builtins());
        let coordinator = InferenceCoordinator::new();

        let results = run_batch_warmup(files.clone(), registry, &coordinator, None, None, None);

        assert_eq!(results.len(), 2);

        // Both files should have signatures in the coordinator (canonical paths).
        let canonical_paths: Vec<PathBuf> = files
            .iter()
            .map(|(p, _)| std::fs::canonicalize(p).unwrap())
            .collect();
        for path in &canonical_paths {
            assert!(
                coordinator.get_signature(path).is_some(),
                "coordinator should have signature for {}",
                path.display()
            );
        }

        // Both results should have inference data.
        for result in &results {
            assert!(
                result.inference_data.check_result.inference.is_some(),
                "{} should have inference result",
                result.path.display()
            );
        }
    }

    #[test]
    fn warmup_empty_input() {
        let registry = Arc::new(TypeAliasRegistry::with_builtins());
        let coordinator = InferenceCoordinator::new();

        let results = run_batch_warmup(vec![], registry, &coordinator, None, None, None);
        assert!(results.is_empty());
    }

    #[test]
    fn warmup_snapshots_have_inference() {
        // Verify that to_snapshot() produces a FileSnapshot with inference data.
        let dir = TempDir::new().unwrap();
        let files = write_nix_files(dir.path(), &[("x.nix", "1 + 2")]);

        let registry = Arc::new(TypeAliasRegistry::with_builtins());
        let coordinator = InferenceCoordinator::new();

        let results = run_batch_warmup(files, registry, &coordinator, None, None, None);
        assert_eq!(results.len(), 1);

        let snap = results[0].to_snapshot();
        assert!(
            snap.inference.is_some(),
            "snapshot should have inference data"
        );
    }
}
