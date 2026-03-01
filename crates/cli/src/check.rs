// ==============================================================================
// `tix check` — Project-level type checking
// ==============================================================================
//
// Type-checks all .nix files in a project using tix.toml configuration.
// Validates that file classifications match their configured contexts and
// reports a summary of errors and warnings.

use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;

use lang_ast::classify::{classify_nix_file, NixFileKind};
use lang_ast::{module_and_source_maps, name_resolution, RootDatabase};
use lang_check::imports::{import_errors_to_diagnostics, resolve_import_types_from_stubs};

use crate::config::{self, TixConfig};
use crate::{build_registry, load_stubs, render_diagnostics};

/// Entry point for `tix check`.
pub fn run_check_project(
    config_path: Option<PathBuf>,
    no_default_stubs: bool,
    verbose: bool,
) -> Result<(), Box<dyn Error>> {
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

    // Step 3: Discover all .nix files.
    let nix_files = config::discover_all_nix_files(&config_dir, &toml_config);

    if nix_files.is_empty() {
        eprintln!("No .nix files found in {}", config_dir.display());
        return Ok(());
    }

    // Step 4: Create shared database.
    let db = RootDatabase::default();

    let mut total_errors = 0usize;
    let mut total_warnings = 0usize;
    let mut config_warnings: Vec<String> = Vec::new();
    let files_count = nix_files.len();

    // Step 5: Process each file.
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

        // Parse + lower.
        let nix_file = match db.read_file(file_path.clone()) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("warning: could not load {}: {e}", relative.display());
                continue;
            }
        };

        let (m, source_map) = module_and_source_maps(&db, nix_file);
        let name_res = name_resolution(&db, nix_file);

        // Classify (AST-only, fast).
        let classification = classify_nix_file(&m, &name_res);

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

        // Resolve context args from tix.toml.
        let context_args =
            config::resolve_context_for_file(file_path, &toml_config, &config_dir, &mut registry)
                .unwrap_or_else(|e| {
                    eprintln!(
                        "warning: failed to resolve context for {}: {e}",
                        relative.display()
                    );
                    HashMap::new()
                });

        // Resolve imports.
        let base_dir = file_path.parent().unwrap_or(std::path::Path::new("/"));
        let import_resolution =
            resolve_import_types_from_stubs(&m, &name_res, base_dir, &HashMap::new());
        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        // Type-check.
        let mut result = lang_check::check_file_collecting(
            &db,
            nix_file,
            &registry,
            import_resolution.types,
            context_args,
        );
        result.diagnostics.extend(import_diagnostics);

        // Handle timeout.
        if result.timed_out {
            let missing_bindings: Vec<smol_str::SmolStr> = m
                .names()
                .filter(|(_, name)| {
                    matches!(
                        name.kind,
                        lang_ast::NameKind::LetIn
                            | lang_ast::NameKind::RecAttrset
                            | lang_ast::NameKind::PlainAttrset
                    )
                })
                .filter(|(id, _)| {
                    result
                        .inference
                        .as_ref()
                        .is_none_or(|inf| inf.name_ty_map.get(*id).is_none())
                })
                .map(|(_, name)| name.text.clone())
                .collect();
            result
                .diagnostics
                .push(lang_check::diagnostic::TixDiagnostic {
                    at_expr: m.entry_expr,
                    kind: lang_check::diagnostic::TixDiagnosticKind::InferenceTimeout {
                        missing_bindings,
                    },
                });
        }

        // Render diagnostics.
        if !result.diagnostics.is_empty() {
            let (errors, warnings) =
                render_diagnostics(file_path, &source_text, &result.diagnostics, &source_map);
            total_errors += errors;
            total_warnings += warnings;
        }
    }

    // Step 6: Print config validation warnings.
    if !config_warnings.is_empty() {
        eprintln!();
        for warning in &config_warnings {
            eprintln!("warning: {warning}");
        }
    }

    // Step 7: Print summary.
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

    // Step 8: Exit code.
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
