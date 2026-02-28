// ==============================================================================
// tix.toml Project Configuration (for LSP)
// ==============================================================================
//
// Mirrors the CLI's config module for discovering and loading `tix.toml` files.
// Provides per-file context resolution for NixOS/Home Manager module typing.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use comment_parser::ParsedTy;
use lang_check::aliases::TypeAliasRegistry;
use serde::Deserialize;
use smol_str::SmolStr;

/// Top-level `tix.toml` configuration.
#[derive(Debug, Default, Deserialize)]
pub struct ProjectConfig {
    /// Global stub file paths or directories (relative to tix.toml).
    #[serde(default)]
    pub stubs: Vec<String>,

    /// Named contexts mapping file globs to module arg types.
    #[serde(default)]
    pub context: HashMap<String, ContextConfig>,

    /// Maximum seconds for type inference on a single file before bailing
    /// out with partial results. Defaults to 10 when omitted.
    #[serde(default)]
    pub deadline: Option<u64>,

    /// Deprecated: no longer used (imports resolve via stubs, not recursive
    /// inference). Kept so existing tix.toml files don't fail to parse.
    #[serde(default)]
    #[allow(dead_code)]
    pub import_deadline: Option<u64>,

    /// Project-wide analysis configuration.
    #[serde(default)]
    pub project: Option<ProjectSection>,
}

/// The `[project]` section of `tix.toml`.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct ProjectSection {
    /// Glob patterns for files to analyze in the background when the LSP
    /// starts. Their inferred types become ephemeral stubs available to all
    /// open files. Patterns are relative to the tix.toml directory.
    ///
    /// Example: `analyze = ["lib/*.nix", "pkgs/**/*.nix"]`
    #[serde(default)]
    pub analyze: Vec<String>,
}

/// A single context definition within `tix.toml`.
#[derive(Debug, Clone, Deserialize)]
pub struct ContextConfig {
    /// Glob patterns for files this context applies to.
    pub paths: Vec<String>,

    /// Stub entries: `@nixos` for built-in, `./path.tix` for user files.
    #[serde(default)]
    pub stubs: Vec<String>,
}

/// Walk up from `start_dir` looking for `tix.toml`. Returns the first match.
pub fn find_config(start_dir: &Path) -> Option<PathBuf> {
    let mut dir = start_dir;
    loop {
        let candidate = dir.join("tix.toml");
        if candidate.is_file() {
            return Some(candidate);
        }
        dir = dir.parent()?;
    }
}

/// Read and parse a `tix.toml` file.
pub fn load_config(path: &Path) -> Result<ProjectConfig, Box<dyn std::error::Error>> {
    let contents = std::fs::read_to_string(path)?;
    let config: ProjectConfig = toml::from_str(&contents)?;
    Ok(config)
}

/// Load a single stub entry. `@`-prefixed entries resolve to built-in context
/// stubs; all others are treated as file/directory paths relative to `config_dir`.
fn load_stub_entry(
    entry: &str,
    config_dir: &Path,
    registry: &mut TypeAliasRegistry,
) -> Result<HashMap<SmolStr, ParsedTy>, Box<dyn std::error::Error>> {
    if let Some(builtin_name) = entry.strip_prefix('@') {
        registry
            .load_context_by_name(builtin_name)
            .ok_or_else(|| format!("Unknown built-in context: @{builtin_name}"))?
    } else {
        let path = config_dir.join(entry);
        let source = std::fs::read_to_string(&path)
            .map_err(|e| format!("Failed to read {}: {e}", path.display()))?;
        registry.load_context_stubs(&source)
    }
}

/// Resolve context args for a file based on `tix.toml` context definitions.
pub fn resolve_context_for_file(
    file_path: &Path,
    config: &ProjectConfig,
    config_dir: &Path,
    registry: &mut TypeAliasRegistry,
) -> Result<HashMap<SmolStr, ParsedTy>, Box<dyn std::error::Error>> {
    let relative = file_path.strip_prefix(config_dir).unwrap_or(file_path);

    for ctx in config.context.values() {
        let matched = ctx.paths.iter().any(|pattern| {
            globset::GlobBuilder::new(pattern)
                .literal_separator(true)
                .build()
                .ok()
                .and_then(|g| g.compile_matcher().is_match(relative).then_some(()))
                .is_some()
        });

        if matched {
            let mut merged = HashMap::new();
            for stub_entry in &ctx.stubs {
                match load_stub_entry(stub_entry, config_dir, registry) {
                    Ok(args) => merged.extend(args),
                    Err(e) => log::warn!("Failed to load context stub '{stub_entry}': {e}"),
                }
            }
            return Ok(merged);
        }
    }

    Ok(HashMap::new())
}

/// Expand the `[project] analyze` glob patterns into concrete file paths.
///
/// Patterns are relative to `config_dir` (the directory containing tix.toml).
/// Returns deduplicated paths. Uses a recursive directory walk + globset
/// matching (no extra `glob` crate dependency).
pub fn resolve_analyze_globs(config: &ProjectConfig, config_dir: &Path) -> Vec<PathBuf> {
    let section = match config.project {
        Some(ref p) if !p.analyze.is_empty() => p,
        _ => return Vec::new(),
    };

    // Build a combined GlobSet from all patterns.
    let mut builder = globset::GlobSetBuilder::new();
    for pattern in &section.analyze {
        match globset::GlobBuilder::new(pattern)
            .literal_separator(true)
            .build()
        {
            Ok(glob) => {
                builder.add(glob);
            }
            Err(e) => {
                log::warn!("Invalid analyze glob pattern '{pattern}': {e}");
            }
        }
    }
    let glob_set = match builder.build() {
        Ok(gs) => gs,
        Err(e) => {
            log::warn!("Failed to build glob set: {e}");
            return Vec::new();
        }
    };

    // Walk the config directory recursively, matching .nix files.
    let mut paths = Vec::new();
    let mut seen = std::collections::HashSet::new();
    walk_dir_matching(config_dir, config_dir, &glob_set, &mut seen, &mut paths);
    paths
}

/// Recursively walk `dir`, matching files against `glob_set` using paths
/// relative to `root`.
fn walk_dir_matching(
    dir: &Path,
    root: &Path,
    glob_set: &globset::GlobSet,
    seen: &mut std::collections::HashSet<PathBuf>,
    out: &mut Vec<PathBuf>,
) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_dir_matching(&path, root, glob_set, seen, out);
        } else if path.is_file() && path.extension().is_some_and(|e| e == "nix") {
            let relative = path.strip_prefix(root).unwrap_or(&path);
            if glob_set.is_match(relative) && seen.insert(path.clone()) {
                out.push(path);
            }
        }
    }
}
