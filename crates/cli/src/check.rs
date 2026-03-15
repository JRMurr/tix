// ==============================================================================
// `tix check` — Project-level type checking
// ==============================================================================
//
// Type-checks all .nix files in a project using tix.toml configuration.
// The pipeline has three phases:
//   1. Sequential Prepare — Salsa queries, classification, context resolution,
//      SyntaxBundle extraction (import resolution deferred to coordinator)
//   2. Parallel Inference — coordinator.demand_batch with demand-driven import
//      resolution across files
//   3. Sequential Render  — deterministic diagnostic output in file order

use std::error::Error;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use dashmap::DashMap;
use lang_ast::classify::{classify_nix_file, NixFileKind};
use lang_ast::{module_and_source_maps, name_resolution, ModuleSourceMap, RootDatabase};
use lang_check::coordinator::{InferenceCoordinator, SyntaxProvider};
use lang_check::SyntaxBundle;
use rayon::prelude::*;

use crate::config::{self, TixConfig};
use crate::timing;
use crate::{build_registry, load_stubs, render_diagnostics};

// ==============================================================================
// CliSyntaxProvider: pre-extracted bundles with Salsa fallback
// ==============================================================================

/// Syntax provider for the CLI. Pre-extracts SyntaxBundles for all known project
/// files during Phase 1 (sequential, single-threaded Salsa access). Files not in
/// the pre-extracted set (transitive imports from outside the project) fall back
/// to on-demand Salsa extraction behind a Mutex.
///
/// Uses DashMap so bundles can be moved out (not cloned) as they're consumed.
/// This is critical for memory: the old pipeline dropped per-file data inside
/// the par_iter closure, and we need to match that behavior.
///
/// Only serves pre-extracted bundles — no on-demand Salsa fallback. Files
/// outside the project set return None (⊤ in the importer). This avoids
/// serialized Salsa parsing during parallel inference.
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
        // serialized Salsa parsing during parallel inference, which would
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
struct FileMetadata {
    file_path: PathBuf,
    source_text: String,
    source_map: ModuleSourceMap,
}

/// Renderable result for a single file (produced by Phase 2).
struct RenderableResult {
    file_path: PathBuf,
    source_text: String,
    source_map: ModuleSourceMap,
    diagnostics: Vec<lang_check::diagnostic::TixDiagnostic>,
    #[allow(dead_code)]
    timed_out: bool,
}

/// Entry point for `tix check`.
pub fn run_check_project(
    config_path: Option<PathBuf>,
    no_default_stubs: bool,
    verbose: bool,
    jobs: Option<usize>,
    show_timing: bool,
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

    // Step 2: Build shared TypeAliasRegistry.
    let mut registry = build_registry(no_default_stubs, &[])?;

    // Load config-level stubs.
    for stub in &toml_config.stubs {
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
    // Phase 1 — Sequential Prepare
    // =========================================================================
    //
    // Salsa queries (parse, lower, nameres, SCC grouping), classification,
    // config validation, and context resolution all run sequentially because
    // the Salsa database is single-threaded.
    //
    // Import resolution is deferred to the coordinator in Phase 2, which
    // resolves imports demand-driven across files.

    // Intermediate data from Phase 1 before the registry is wrapped in Arc.
    struct PrePreparedFile {
        file_path: PathBuf,
        source_text: String,
        source_map: ModuleSourceMap,
        module: lang_ast::Module,
        module_indices: lang_ast::ModuleIndices,
        name_res: lang_ast::NameResolution,
        grouped_defs: lang_ast::GroupedDefs,
        context_args: Arc<std::collections::HashMap<smol_str::SmolStr, comment_parser::ParsedTy>>,
    }

    let db = RootDatabase::default();
    let mut pre_prepared: Vec<PrePreparedFile> = Vec::with_capacity(files_count);
    let mut config_warnings: Vec<String> = Vec::new();

    for file_path in &nix_files {
        let relative = file_path
            .strip_prefix(&config_dir)
            .unwrap_or(file_path)
            .to_path_buf();

        // Read source.
        let source_text = match std::fs::read_to_string(file_path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: could not read {}: {e}", relative.display());
                continue;
            }
        };

        // Parse + lower via Salsa.
        let nix_file = match db.read_file(file_path.clone()) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("warning: could not load {}: {e}", relative.display());
                continue;
            }
        };

        let (module, source_map) = module_and_source_maps(&db, nix_file);
        let name_res = name_resolution(&db, nix_file);

        // Classify (AST-only, fast).
        let classification = classify_nix_file(&module, &name_res);

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
        if let Some(warning) =
            validate_classification(file_path, &classification, &toml_config, &config_dir)
        {
            config_warnings.push(warning);
        }

        // Resolve context args from tix.toml (may mutate registry).
        let context_args =
            config::resolve_context_for_file(file_path, &toml_config, &config_dir, &mut registry)
                .unwrap_or_else(|e| {
                    eprintln!(
                        "warning: failed to resolve context for {}: {e}",
                        relative.display()
                    );
                    Arc::default()
                });

        // Remaining Salsa queries for inference.
        let module_indices = lang_ast::module_indices(&db, nix_file);
        let grouped_defs = lang_ast::group_def(&db, nix_file);

        pre_prepared.push(PrePreparedFile {
            file_path: file_path.clone(),
            source_text,
            source_map,
            module,
            module_indices,
            name_res,
            grouped_defs,
            context_args,
        });
    }

    // Wrap registry in Arc now that all mutations (context resolution) are done.
    // Each file shares a single ref-counted registry instead of deep-cloning it.
    let registry = Arc::new(registry);

    let precomputed: DashMap<PathBuf, SyntaxBundle> = DashMap::with_capacity(pre_prepared.len());
    let mut metadata: Vec<FileMetadata> = Vec::with_capacity(pre_prepared.len());
    for pp in pre_prepared {
        metadata.push(FileMetadata {
            file_path: pp.file_path.clone(),
            source_text: pp.source_text,
            source_map: pp.source_map,
        });
        precomputed.insert(
            pp.file_path.clone(),
            SyntaxBundle {
                path: pp.file_path,
                module: pp.module,
                module_indices: pp.module_indices,
                name_res: pp.name_res,
                grouped_defs: pp.grouped_defs,
                registry: Arc::clone(&registry),
                context_args: pp.context_args,
                deadline_secs: toml_config.deadline,
            },
        );
    }
    timer.mark("prepare (sequential)");

    let syntax_provider = CliSyntaxProvider { precomputed };

    // =========================================================================
    // Phase 2 — Parallel Inference with demand-driven import resolution
    // =========================================================================
    //
    // The coordinator infers all files in parallel via rayon. When a file
    // imports another, the coordinator recursively infers the dependency
    // first. Each file is inferred at most once (results cached in the
    // coordinator's DashMap).
    //
    // Critical memory optimization: the InferenceResult (ArenaMap<NameId/ExprId,
    // OutputTy>) is dropped per-file inside the par_iter closure, before
    // .collect() gathers all results. This reduces peak memory by ~70% when
    // checking many files in parallel.

    let coordinator = InferenceCoordinator::new();
    let results: Vec<RenderableResult> = metadata
        .into_par_iter()
        .map(|fm| {
            tracing::info!("inference start: {}", fm.file_path.display());
            let result = coordinator.demand_file(&fm.file_path, &syntax_provider, None);
            tracing::info!("inference done:  {}", fm.file_path.display());

            // Extract only diagnostics + timed_out. The heavy InferenceResult
            // (full OutputTy maps for every name and expression) is dropped
            // here, matching the old pipeline's memory behavior.
            let (diagnostics, timed_out) = result
                .map(|cr| (cr.check_result.diagnostics, cr.check_result.timed_out))
                .unwrap_or_default();

            RenderableResult {
                file_path: fm.file_path,
                source_text: fm.source_text,
                source_map: fm.source_map,
                diagnostics,
                timed_out,
            }
        })
        .collect();
    timer.mark("inference (parallel)");

    // =========================================================================
    // Phase 3 — Sequential Render
    // =========================================================================
    //
    // Iterate results in file order to produce deterministic diagnostic output.

    let mut total_errors = 0usize;
    let mut total_warnings = 0usize;

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
    config: &TixConfig,
    config_dir: &std::path::Path,
) -> Option<String> {
    // Skip low-confidence classifications.
    if classification.confidence < 0.5 {
        return None;
    }

    let relative = file_path.strip_prefix(config_dir).unwrap_or(file_path);

    let expected = expected_context_name(classification.kind);
    let actual = config::find_matching_context(file_path, config, config_dir);

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
