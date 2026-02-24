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

    /// Maximum seconds for type inference per imported file. Defaults to 5
    /// when omitted.
    #[serde(default)]
    pub import_deadline: Option<u64>,
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
