// ==============================================================================
// `tix check` — Project-level type checking
// ==============================================================================
//
// Type-checks all .nix files in a project using tix.toml configuration.
// The pipeline has four phases:
//   1a.  Parallel File I/O  — canonicalize + read all .nix files
//   1b.  Parallel Syntax    — parse, lower, name resolution, SCC grouping (rayon)
//   1b'. Sequential Metadata — classification, context resolution, import scanning
//   1.5  Dependency Graph   — SCC computation + topological layering
//   2.   Layered Inference  — layer-by-layer parallel inference with cross-file
//        type flow and reference-counted signature eviction
//   3.   Sequential Render  — deterministic diagnostic output in file order

use std::collections::HashMap;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use dashmap::DashMap;
use lang_ast::classify::{classify_nix_file, NixFileKind};
use lang_ast::ModuleSourceMap;
use lang_check::coordinator::{InferenceCoordinator, SyntaxProvider};
use lang_check::SyntaxBundle;
use rayon::prelude::*;
use rowan::ast::AstNode;

use crate::config::{self, TixConfig};
use crate::json_output;
use crate::timing;
use crate::{build_registry, load_stubs, render_diagnostics, OutputFormat};

// ==============================================================================
// CliSyntaxProvider: pre-extracted bundles
// ==============================================================================

/// Syntax provider for the CLI. Pre-extracts SyntaxBundles for all known project
/// files during Phase 1 (sequential). Files not in the pre-extracted set
/// (transitive imports from outside the project) return None (top in the importer).
///
/// Uses DashMap so bundles can be moved out (not cloned) as they're consumed.
/// This is critical for memory: the old pipeline dropped per-file data inside
/// the par_iter closure, and we need to match that behavior.
struct CliSyntaxProvider {
    precomputed: DashMap<PathBuf, SyntaxBundle>,
}

impl SyntaxProvider for CliSyntaxProvider {
    fn syntax_for_file(&self, path: &Path) -> Option<SyntaxBundle> {
        // Move out of precomputed (each file consumed at most once by the
        // coordinator's demand_file, so we won't need it again).
        //
        // Files not in the precomputed set (transitive imports from outside
        // the project) return None — they get ⊤ in the importer. This avoids
        // on-demand parsing during parallel inference, which would
        // destroy throughput on large projects like nixpkgs (42K files).
        // The single-file `tixc` command has its own SyntaxProvider that does
        // on-demand parsing for transitive imports.
        self.precomputed.remove(path).map(|(_, bundle)| bundle)
    }
}

// ==============================================================================
// Phase 1 data: metadata retained for rendering (not part of SyntaxBundle)
// ==============================================================================

/// Per-file rendering metadata collected during Phase 1. SyntaxBundles go to
/// the coordinator; this struct holds what Phase 3 needs for diagnostics.
/// The file path is not stored here — it's the key in the DashMap and returned
/// on removal.
struct FileMetadata {
    source_text: String,
    source_map: ModuleSourceMap,
}

/// Renderable result for a single file (produced by Phase 2).
struct RenderableResult {
    file_path: PathBuf,
    source_text: String,
    source_map: ModuleSourceMap,
    diagnostics: Vec<lang_check::diagnostic::TixDiagnostic>,
    /// `true` if the file has `# tix-nocheck` — all diagnostics suppressed.
    nocheck: bool,
    /// 0-indexed lines where diagnostics are suppressed (`# tix-ignore`).
    ignore_lines: std::collections::HashSet<u32>,
}

/// Intermediate result from inference (before combining with metadata for rendering).
struct InferBundleResult {
    diagnostics: Vec<lang_check::diagnostic::TixDiagnostic>,
    nocheck: bool,
    ignore_lines: std::collections::HashSet<u32>,
    bailed_out: bool,
}

/// Infer a file from a pre-extracted SyntaxBundle and cache its signature.
/// Shared by both the single-pass path and fixpoint iteration.
fn infer_bundle(
    coordinator: &InferenceCoordinator,
    file_path: &Path,
    bundle: SyntaxBundle,
) -> InferBundleResult {
    let base_dir = file_path.parent().unwrap_or(Path::new("/"));

    let import_resolution = coordinator.resolve_imports(
        &bundle.module,
        &bundle.name_res,
        base_dir,
        Some(&bundle.registry),
    );
    let import_diagnostics =
        lang_check::imports::import_errors_to_diagnostics(&import_resolution.errors);

    let inputs = lang_check::InferenceInputs {
        module: bundle.module,
        module_indices: bundle.module_indices,
        name_res: bundle.name_res,
        grouped_defs: bundle.grouped_defs,
        registry: bundle.registry,
        import_types: import_resolution.types,
        import_diagnostics,
        context_args: bundle.context_args,
        rss_limit_mb: None,
        file_path: Some(file_path.to_path_buf()),
        imported_type_exports: std::collections::HashMap::new(),
        typeof_import_types: std::collections::HashMap::new(),
        file_base_dir: None,
    };

    let check_result = lang_check::run_inference(&inputs);

    if let Some(sig) = lang_check::extract_file_signature(&check_result, inputs.module.entry_expr) {
        coordinator.set_signature(file_path, sig);
    }

    InferBundleResult {
        diagnostics: check_result.diagnostics,
        nocheck: inputs.module.nocheck,
        ignore_lines: inputs.module.ignore_lines.clone(),
        bailed_out: check_result.bailed_out,
    }
}

/// Entry point for `tix check`.
pub fn run_check_project(
    config_path: Option<PathBuf>,
    no_default_stubs: bool,
    verbose: bool,
    jobs: Option<usize>,
    show_timing: bool,
    format: OutputFormat,
) -> Result<(), Box<dyn Error>> {
    let mut timer = timing::Timer::new(show_timing);

    // Configure rayon thread pool. Use 16 MB stacks (matching the LSP) so
    // deeply recursive inference on large generated files (e.g.
    // hackage-packages.nix) doesn't blow the default 8 MB stack.
    {
        let mut builder = rayon::ThreadPoolBuilder::new().stack_size(16 * 1024 * 1024);
        if let Some(n) = jobs {
            builder = builder.num_threads(n);
        }
        builder.build_global().ok(); // Ignored if pool already initialized.
    }

    // Step 1: Find and load tix.toml.
    let (toml_config, config_dir) = find_and_load_config(config_path)?;
    let compiled_contexts = config::CompiledContexts::new(&toml_config);

    // Step 2: Build shared TypeAliasRegistry.
    let mut registry = build_registry(no_default_stubs, &[])?;

    // Runtime stub generation.
    crate::maybe_generate_stubs(&mut registry, &toml_config.stubs, &config_dir);

    // Load config-level stubs.
    for stub in toml_config.stubs.paths() {
        let stub_path = config_dir.join(stub);
        if let Err(e) = load_stubs(&mut registry, &stub_path) {
            eprintln!(
                "warning: failed to load config stub '{}': {e}",
                stub_path.display()
            );
        }
    }

    if let Err(cycles) = registry.validate() {
        eprintln!("error: cyclic type aliases detected: {:?}", cycles);
        std::process::exit(1);
    }
    timer.mark("registry+stubs");

    // Step 3: Discover all .nix files.
    let nix_files = config::discover_all_nix_files(&config_dir, &toml_config);

    if nix_files.is_empty() {
        eprintln!("No .nix files found in {}", config_dir.display());
        return Ok(());
    }

    let files_count = nix_files.len();

    // =========================================================================
    // Phase 1a — Parallel File I/O
    // =========================================================================
    //
    // Front-load all disk I/O (canonicalize + read) in parallel. This avoids
    // sequential syscalls for 42K+ files in large projects like nixpkgs.

    struct PrereadFile {
        original_path: PathBuf,
        canonical_path: PathBuf,
        contents: String,
    }

    let preread: Vec<PrereadFile> = nix_files
        .par_iter()
        .filter_map(|file_path| {
            let canonical_path = std::fs::canonicalize(file_path).ok()?;
            let contents = std::fs::read_to_string(&canonical_path).ok()?;
            Some(PrereadFile {
                original_path: file_path.clone(),
                canonical_path,
                contents,
            })
        })
        .collect();

    timer.mark("file I/O (parallel)");

    // =========================================================================
    // Phase 1b — Parallel Syntax Processing
    // =========================================================================
    //
    // Parse, lower, name resolution, SCC grouping — pure per-file computation
    // parallelized via rayon. This is the expensive step (~ms per file).

    let syntax_results: Vec<(PrereadFile, lang_ast::SyntaxResult)> = preread
        .into_par_iter()
        .map(|pf| {
            let r = lang_ast::run_syntax_pipeline_for_file(&pf.canonical_path, &pf.contents);
            (pf, r)
        })
        .collect();

    timer.mark("syntax pipeline (parallel)");

    // =========================================================================
    // Phase 1b-seq — Sequential Metadata Collection
    // =========================================================================
    //
    // Classification, config validation, context resolution (mutates registry),
    // and import scanning. All lightweight (~μs per file).

    struct PrePreparedFile {
        canonical_path: PathBuf,
        source_text: String,
        source_map: ModuleSourceMap,
        module: lang_ast::Module,
        module_indices: lang_ast::ModuleIndices,
        name_res: lang_ast::NameResolution,
        grouped_defs: lang_ast::GroupedDefs,
        context_args: Arc<std::collections::HashMap<smol_str::SmolStr, comment_parser::ParsedTy>>,
        import_targets: Vec<PathBuf>,
    }

    let mut pre_prepared: Vec<PrePreparedFile> = Vec::with_capacity(syntax_results.len());
    let mut config_warnings: Vec<String> = Vec::new();

    for (pf, r) in syntax_results {
        let relative = pf
            .original_path
            .strip_prefix(&config_dir)
            .unwrap_or(&pf.original_path)
            .to_path_buf();

        // Classify (AST-only, fast).
        let classification = classify_nix_file(&r.module, &r.name_res);

        if verbose {
            eprintln!(
                "  {} — {} (confidence: {:.0}%, {})",
                relative.display(),
                classification.kind,
                classification.confidence * 100.0,
                classification.reason,
            );
        }

        // Config validation: compare classification vs tix.toml context.
        if let Some(warning) = validate_classification(
            &pf.original_path,
            &classification,
            &compiled_contexts,
            &config_dir,
        ) {
            config_warnings.push(warning);
        }

        // Resolve context args from tix.toml (may mutate registry).
        let context_args = config::resolve_context_for_file(
            &pf.original_path,
            &toml_config,
            &config_dir,
            &mut registry,
        )
        .unwrap_or_else(|e| {
            eprintln!(
                "warning: failed to resolve context for {}: {e}",
                relative.display()
            );
            Arc::default()
        });

        // Scan imports for the file-level dependency graph (Phase 1.5).
        let base_dir = pf
            .canonical_path
            .parent()
            .unwrap_or(std::path::Path::new("/"));
        let import_targets =
            lang_check::imports::scan_all_import_paths(&r.module, &r.name_res, base_dir);

        pre_prepared.push(PrePreparedFile {
            canonical_path: pf.canonical_path,
            source_text: pf.contents,
            source_map: r.source_map,
            module: r.module,
            module_indices: r.module_indices,
            name_res: r.name_res,
            grouped_defs: r.grouped_defs,
            context_args,
            import_targets,
        });
    }
    timer.mark("metadata (sequential)");

    // Wrap registry in Arc now that all mutations (context resolution) are done.
    // Each file shares a single ref-counted registry instead of deep-cloning it.
    let registry = Arc::new(registry);

    let precomputed: DashMap<PathBuf, SyntaxBundle> = DashMap::with_capacity(pre_prepared.len());
    let metadata_map: DashMap<PathBuf, FileMetadata> = DashMap::with_capacity(pre_prepared.len());
    let mut import_edges: HashMap<PathBuf, Vec<PathBuf>> =
        HashMap::with_capacity(pre_prepared.len());
    let mut expr_counts: HashMap<PathBuf, usize> = HashMap::with_capacity(pre_prepared.len());

    // Track original discovery order for deterministic Phase 3 output.
    let mut file_order: Vec<PathBuf> = Vec::with_capacity(pre_prepared.len());

    for pp in pre_prepared {
        // canonical_path was already computed during parallel pre-read.
        file_order.push(pp.canonical_path.clone());
        expr_counts.insert(pp.canonical_path.clone(), pp.module.exprs().len());
        import_edges.insert(pp.canonical_path.clone(), pp.import_targets);
        metadata_map.insert(
            pp.canonical_path.clone(),
            FileMetadata {
                source_text: pp.source_text,
                source_map: pp.source_map,
            },
        );
        precomputed.insert(
            pp.canonical_path.clone(),
            SyntaxBundle {
                path: pp.canonical_path,
                module: pp.module,
                module_indices: pp.module_indices,
                name_res: pp.name_res,
                grouped_defs: pp.grouped_defs,
                registry: Arc::clone(&registry),
                context_args: pp.context_args,
            },
        );
    }

    // =========================================================================
    // Phase 1.5 — Build file-level dependency graph and layers
    // =========================================================================
    //
    // Compute SCCs on the file import graph and topologically sort into layers.
    // Layer 0 = leaf files with no in-project dependencies (inferred first).
    // Each subsequent layer's dependencies are guaranteed to be cached from
    // prior layers.

    let layers = lang_check::file_graph::build_file_layers_with_sccs(&import_edges);
    let mut importer_counts = lang_check::file_graph::compute_importer_counts(&import_edges);
    timer.mark("dependency graph");

    let syntax_provider = CliSyntaxProvider { precomputed };

    // =========================================================================
    // Phase 2 — Layered Parallel Inference with cross-file type flow
    // =========================================================================
    //
    // Files are inferred layer-by-layer, SCC-by-SCC within each layer.
    // Dependencies from prior layers have their signatures cached in the
    // coordinator, so import resolution gets real types instead of ⊤.
    //
    // Non-cyclic SCCs (single files) are inferred once. Cyclic SCCs (mutual
    // imports) are iterated until signatures stabilize or the iteration cap
    // is reached, giving real types across cycle edges.
    //
    // Memory optimization: reference-counted eviction drops signatures whose
    // importers have all been processed, keeping the live set bounded to the
    // "frontier" rather than the entire project.

    // Files with more than this many expressions run sequentially within their
    // layer to avoid concurrent memory spikes that cause OOM on large projects.
    const HEAVY_FILE_EXPR_THRESHOLD: usize = 20_000;
    /// Maximum fixpoint iterations for cyclic SCCs. Most cycles converge in
    /// 2-3 rounds; 4 is a conservative cap.
    const MAX_FIXPOINT_ROUNDS: usize = 4;

    let coordinator = InferenceCoordinator::new();
    let mut all_results: Vec<RenderableResult> = Vec::with_capacity(files_count);

    // Shared inference logic for a single file. Consumes the bundle from the
    // syntax provider and metadata from the metadata map.
    let infer_one = |path: &PathBuf| -> Option<RenderableResult> {
        let (file_path, fm) = metadata_map.remove(path)?;

        let expr_count = expr_counts.get(path).copied().unwrap_or(0);
        tracing::debug!(
            file = %lang_ast::display_path(&file_path),
            exprs = expr_count,
            rss_mb = format_args!("{:.0}", lang_check::rss_mb()),
            "starting file"
        );

        let bundle = match syntax_provider.syntax_for_file(&file_path) {
            Some(b) => b,
            None => {
                return Some(RenderableResult {
                    file_path,
                    source_text: fm.source_text,
                    source_map: fm.source_map,
                    diagnostics: vec![],
                    nocheck: false,
                    ignore_lines: Default::default(),
                });
            }
        };

        let result = infer_bundle(&coordinator, &file_path, bundle);

        tracing::debug!(
            file = %lang_ast::display_path(&file_path),
            rss_mb = format_args!("{:.0}", lang_check::rss_mb()),
            diags = result.diagnostics.len(),
            bailed_out = result.bailed_out,
            "finished file"
        );

        Some(RenderableResult {
            file_path,
            source_text: fm.source_text,
            source_map: fm.source_map,
            diagnostics: result.diagnostics,
            nocheck: result.nocheck,
            ignore_lines: result.ignore_lines,
        })
    };

    for (layer_idx, layer) in layers.iter().enumerate() {
        let layer_file_count: usize = layer.sccs.iter().map(|s| s.files.len()).sum();
        tracing::debug!(
            layer = layer_idx,
            files = layer_file_count,
            sccs = layer.sccs.len(),
            rss_mb = format_args!("{:.0}", lang_check::rss_mb()),
            "starting layer"
        );

        // =================================================================
        // Non-cyclic files: batch all singletons across SCCs for parallel
        // inference, preserving the original par_iter parallelism.
        // =================================================================
        let non_cyclic_files: Vec<&PathBuf> = layer
            .sccs
            .iter()
            .filter(|scc| !scc.is_cyclic)
            .flat_map(|scc| scc.files.iter())
            .collect();

        if !non_cyclic_files.is_empty() {
            let (heavy, light): (Vec<&PathBuf>, Vec<&PathBuf>) =
                non_cyclic_files.into_iter().partition(|p| {
                    expr_counts.get(*p).copied().unwrap_or(0) > HEAVY_FILE_EXPR_THRESHOLD
                });

            if !heavy.is_empty() {
                tracing::info!(
                    "layer {} has {} heavy file(s) (>{} exprs), running sequentially: {}",
                    layer_idx,
                    heavy.len(),
                    HEAVY_FILE_EXPR_THRESHOLD,
                    heavy
                        .iter()
                        .map(|p| format!(
                            "{} ({})",
                            p.file_name().unwrap_or_default().to_string_lossy(),
                            expr_counts.get(*p).unwrap_or(&0)
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            let heavy_results: Vec<RenderableResult> =
                heavy.iter().filter_map(|p| infer_one(p)).collect();
            let light_results: Vec<RenderableResult> =
                light.par_iter().filter_map(|p| infer_one(p)).collect();

            all_results.extend(heavy_results);
            all_results.extend(light_results);
        }

        // =================================================================
        // Cyclic SCCs: fixpoint iteration (sequential within each SCC)
        // =================================================================
        for scc in layer.sccs.iter().filter(|scc| scc.is_cyclic) {
            // =============================================================
            // Cyclic SCC: fixpoint iteration
            // =============================================================
            //
            // Clone bundles for reuse across rounds. Metadata is extracted
            // once and held aside — only the final round's diagnostics are
            // kept.
            tracing::info!(
                "layer {}: cyclic SCC with {} files, up to {} fixpoint rounds",
                layer_idx,
                scc.files.len(),
                MAX_FIXPOINT_ROUNDS,
            );

            // Pre-extract bundles (clone for reuse) and metadata.
            let scc_bundles: HashMap<PathBuf, SyntaxBundle> = scc
                .files
                .iter()
                .filter_map(|p| {
                    syntax_provider
                        .precomputed
                        .get(p)
                        .map(|entry| (p.clone(), entry.value().clone()))
                })
                .collect();

            let scc_metadata: HashMap<PathBuf, FileMetadata> = scc
                .files
                .iter()
                .filter_map(|p| metadata_map.remove(p))
                .collect();

            let mut last_results: Vec<RenderableResult> = Vec::new();

            for round in 0..MAX_FIXPOINT_ROUNDS {
                // Snapshot signatures before this round for convergence check.
                let prev_sigs: HashMap<PathBuf, Option<lang_ty::OwnedTy>> = scc
                    .files
                    .iter()
                    .map(|p| (p.clone(), coordinator.get_signature(p)))
                    .collect();

                last_results.clear();

                // Infer all files in the SCC sequentially within each round.
                // Sequential ensures deterministic convergence: each file in
                // round N sees all of round N-1's signatures (Jacobi-style
                // within a round, since we snapshot above).
                for path in &scc.files {
                    let Some(bundle) = scc_bundles.get(path).cloned() else {
                        continue;
                    };

                    let file_path = path.clone();
                    let result = infer_bundle(&coordinator, &file_path, bundle);

                    if let Some(fm) = scc_metadata.get(path) {
                        last_results.push(RenderableResult {
                            file_path,
                            source_text: fm.source_text.clone(),
                            source_map: fm.source_map.clone(),
                            diagnostics: result.diagnostics,
                            nocheck: result.nocheck,
                            ignore_lines: result.ignore_lines,
                        });
                    }
                }

                // Skip convergence check on the first round — there are no
                // previous signatures to compare against.
                if round == 0 {
                    continue;
                }

                // Check convergence: all signatures structurally unchanged.
                let converged = scc.files.iter().all(|p| {
                    let new_sig = coordinator.get_signature(p);
                    match (&prev_sigs[p], &new_sig) {
                        (Some(old), Some(new)) => old.structurally_eq(new),
                        (None, None) => true,
                        _ => false,
                    }
                });

                if converged {
                    tracing::info!(
                        "cyclic SCC ({} files) converged after {} round(s)",
                        scc.files.len(),
                        round + 1,
                    );
                    break;
                }
            }

            // Remove consumed bundles from the syntax provider.
            for path in &scc.files {
                syntax_provider.precomputed.remove(path);
            }

            all_results.extend(last_results);
        }

        // Reference-counted eviction: decrement importer counts for each
        // dependency of files in this layer. Evict signatures whose count
        // reaches 0 (all importers have been processed).
        let mut to_evict = Vec::new();
        for file in layer.all_files() {
            if let Some(deps) = import_edges.get(file) {
                for dep in deps {
                    if let Some(count) = importer_counts.get_mut(dep) {
                        *count -= 1;
                        if *count == 0 {
                            to_evict.push(dep.clone());
                        }
                    }
                }
            }
        }
        if !to_evict.is_empty() {
            coordinator.remove_signatures_batch(&to_evict);
        }
    }

    // Sort results back into original file discovery order for deterministic
    // Phase 3 output.
    let order_index: HashMap<&PathBuf, usize> =
        file_order.iter().enumerate().map(|(i, p)| (p, i)).collect();
    all_results.sort_by_key(|r| order_index.get(&r.file_path).copied().unwrap_or(usize::MAX));

    let results = all_results;
    timer.mark("inference (layered)");

    // =========================================================================
    // Phase 3 — Sequential Render
    // =========================================================================
    //
    // Iterate results in file order to produce deterministic diagnostic output.

    let mut total_errors = 0usize;
    let mut total_warnings = 0usize;

    // Apply suppression directives before rendering.
    let results: Vec<RenderableResult> = results
        .into_iter()
        .map(|mut r| {
            if r.nocheck {
                r.diagnostics.clear();
            } else if !r.ignore_lines.is_empty() {
                let root = rnix::Root::parse(&r.source_text).tree();
                r.diagnostics = lang_check::diagnostic::filter_ignored_diagnostics(
                    r.diagnostics,
                    &r.ignore_lines,
                    &r.source_map,
                    root.syntax(),
                    &r.source_text,
                );
            }
            r
        })
        .collect();

    match format {
        OutputFormat::Human => {
            for result in &results {
                if !result.diagnostics.is_empty() {
                    let (errors, warnings) = render_diagnostics(
                        &result.file_path,
                        &result.source_text,
                        &result.diagnostics,
                        &result.source_map,
                    );
                    total_errors += errors;
                    total_warnings += warnings;
                }
            }

            // Print config validation warnings.
            if !config_warnings.is_empty() {
                eprintln!();
                for warning in &config_warnings {
                    eprintln!("warning: {warning}");
                }
            }

            // Print summary.
            eprintln!(
                "\nChecked {} files: {} errors, {} warnings",
                files_count, total_errors, total_warnings
            );

            if !config_warnings.is_empty() {
                eprintln!(
                    "  ({} config suggestions — run with --verbose for details)",
                    config_warnings.len()
                );
            }
        }
        OutputFormat::Json => {
            let mut json_files = Vec::with_capacity(results.len());

            for result in &results {
                let (file_result, errors, warnings) = json_output::diagnostics_to_json(
                    &result.file_path,
                    &result.source_text,
                    &result.diagnostics,
                    &result.source_map,
                );
                total_errors += errors;
                total_warnings += warnings;
                // Only include files that have diagnostics.
                if !file_result.diagnostics.is_empty() {
                    json_files.push(file_result);
                }
            }

            let output = json_output::JsonOutput {
                version: 1,
                files: json_files,
                summary: json_output::JsonSummary {
                    files_checked: files_count,
                    errors: total_errors,
                    warnings: total_warnings,
                },
                bindings: None,
                root_type: None,
            };

            json_output::write_json_output(&output)?;
        }
    }

    timer.mark("render");
    timer.summary();

    // Exit code.
    if total_errors > 0 {
        std::process::exit(1);
    }

    Ok(())
}

// ==============================================================================
// Config Discovery
// ==============================================================================

/// Find and load tix.toml configuration. Returns the config and its directory.
fn find_and_load_config(
    config_path: Option<PathBuf>,
) -> Result<(TixConfig, PathBuf), Box<dyn Error>> {
    match config_path {
        Some(explicit_path) => {
            let cfg = config::load_config(&explicit_path)?;
            let dir = explicit_path
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(std::path::Path::new("."))
                .to_path_buf();
            let dir = std::fs::canonicalize(&dir).unwrap_or(dir);
            Ok((cfg, dir))
        }
        None => {
            let cwd = std::env::current_dir()?;
            match config::find_config(&cwd) {
                Some(found_path) => {
                    let cfg = config::load_config(&found_path)?;
                    let dir = found_path
                        .parent()
                        .unwrap_or(std::path::Path::new("."))
                        .to_path_buf();
                    Ok((cfg, dir))
                }
                None => Err(
                    "tix.toml not found. Run `tix init` to generate one, or use --config to specify a path."
                        .into(),
                ),
            }
        }
    }
}

// ==============================================================================
// Config Validation
// ==============================================================================

/// Map NixFileKind to expected context name (if any).
fn expected_context_name(kind: NixFileKind) -> Option<&'static str> {
    match kind {
        NixFileKind::NixosModule => Some("nixos"),
        NixFileKind::HomeManagerModule => Some("home-manager"),
        NixFileKind::CallPackage => Some("callpackage"),
        // Overlay, Library, PlainExpression, Flake — no context expected.
        _ => None,
    }
}

/// Validate that a file's classification matches its tix.toml context assignment.
fn validate_classification(
    file_path: &std::path::Path,
    classification: &lang_ast::classify::Classification,
    compiled_contexts: &config::CompiledContexts,
    config_dir: &std::path::Path,
) -> Option<String> {
    // Skip low-confidence classifications.
    if classification.confidence < 0.5 {
        return None;
    }

    let relative = file_path.strip_prefix(config_dir).unwrap_or(file_path);

    let expected = expected_context_name(classification.kind);
    let actual = compiled_contexts.find_matching(file_path, config_dir);

    match (expected, actual) {
        // File needs a context but doesn't have one in config.
        (Some(expected_ctx), None) => Some(format!(
            "{} looks like a {} but isn't in any context (expected [context.{}])",
            relative.display(),
            classification.kind,
            expected_ctx,
        )),
        // File's config context disagrees with classification.
        (Some(expected_ctx), Some(actual_ctx))
            if !contexts_compatible(expected_ctx, actual_ctx) =>
        {
            Some(format!(
                "{} is in [context.{}] but looks like a {} (expected [context.{}])",
                relative.display(),
                actual_ctx,
                classification.kind,
                expected_ctx,
            ))
        }
        _ => None,
    }
}

/// Check if two context names are compatible (allowing aliases).
fn contexts_compatible(expected: &str, actual: &str) -> bool {
    if expected == actual {
        return true;
    }
    // Allow common aliases: "home" for "home-manager", "hm" for "home-manager".
    matches!(
        (expected, actual),
        ("home-manager", "home")
            | ("home-manager", "hm")
            | ("callpackage", "pkgs")
            | ("callpackage", "packages")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expected_context_for_kinds() {
        assert_eq!(
            expected_context_name(NixFileKind::NixosModule),
            Some("nixos")
        );
        assert_eq!(
            expected_context_name(NixFileKind::HomeManagerModule),
            Some("home-manager")
        );
        assert_eq!(
            expected_context_name(NixFileKind::CallPackage),
            Some("callpackage")
        );
        assert_eq!(expected_context_name(NixFileKind::Overlay), None);
        assert_eq!(expected_context_name(NixFileKind::Library), None);
        assert_eq!(expected_context_name(NixFileKind::PlainExpression), None);
    }

    #[test]
    fn contexts_compatible_aliases() {
        assert!(contexts_compatible("home-manager", "home-manager"));
        assert!(contexts_compatible("home-manager", "home"));
        assert!(contexts_compatible("home-manager", "hm"));
        assert!(contexts_compatible("callpackage", "pkgs"));
        assert!(!contexts_compatible("nixos", "home-manager"));
    }
}
