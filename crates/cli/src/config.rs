// ==============================================================================
// tix.toml Configuration
// ==============================================================================
//
// Discovers and loads `tix.toml` project configuration files. Provides:
// - Global stub paths (additive to CLI `--stubs`)
// - Context definitions that map file globs to module arg types
//
// Example tix.toml:
//
// ```toml
// stubs = ["./stubs"]
//
// [context.nixos]
// paths = ["modules/**/*.nix", "nixos/**/*.nix"]
// stubs = ["@nixos"]
//
// [context.home]
// paths = ["home/**/*.nix"]
// stubs = ["@home-manager", "./stubs/home-extra.tix"]
// ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use comment_parser::ParsedTy;
use lang_check::aliases::TypeAliasRegistry;
use serde::Deserialize;
use smol_str::SmolStr;

/// Top-level `tix.toml` configuration.
#[derive(Debug, Default, Deserialize)]
pub struct TixConfig {
    /// Global stub file paths or directories (relative to tix.toml).
    #[serde(default)]
    pub stubs: Vec<String>,

    /// Named contexts mapping file globs to module arg types.
    #[serde(default)]
    pub context: HashMap<String, ContextConfig>,
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
pub fn load_config(path: &Path) -> Result<TixConfig, Box<dyn std::error::Error>> {
    let contents = std::fs::read_to_string(path)?;
    let config: TixConfig = toml::from_str(&contents)?;
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
///
/// Checks the file path against each context's glob patterns. If a match is
/// found, loads the context's stubs and returns the merged arg→type map.
/// Returns an empty map if no context matches.
pub fn resolve_context_for_file(
    file_path: &Path,
    config: &TixConfig,
    config_dir: &Path,
    registry: &mut TypeAliasRegistry,
) -> Result<HashMap<SmolStr, ParsedTy>, Box<dyn std::error::Error>> {
    // Compute the file path relative to the config dir for glob matching.
    let relative = file_path.strip_prefix(config_dir).unwrap_or(file_path);

    for ctx in config.context.values() {
        let matched = ctx.paths.iter().any(|pattern| {
            globset::Glob::new(pattern)
                .ok()
                .and_then(|g| g.compile_matcher().is_match(relative).then_some(()))
                .is_some()
        });

        if matched {
            let mut merged = HashMap::new();
            for stub_entry in &ctx.stubs {
                match load_stub_entry(stub_entry, config_dir, registry) {
                    Ok(args) => merged.extend(args),
                    Err(e) => eprintln!("Warning: failed to load context stub '{stub_entry}': {e}"),
                }
            }
            return Ok(merged);
        }
    }

    Ok(HashMap::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_minimal_config() {
        let toml_str = r#"
            stubs = ["./stubs"]
        "#;
        let config: TixConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(config.stubs, vec!["./stubs"]);
        assert!(config.context.is_empty());
    }

    #[test]
    fn parse_config_with_contexts() {
        let toml_str = r#"
            stubs = ["./stubs"]

            [context.nixos]
            paths = ["modules/**/*.nix"]
            stubs = ["@nixos"]

            [context.home]
            paths = ["home/**/*.nix"]
            stubs = ["@home-manager", "./stubs/home.tix"]
        "#;
        let config: TixConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(config.context.len(), 2);

        let nixos = &config.context["nixos"];
        assert_eq!(nixos.paths, vec!["modules/**/*.nix"]);
        assert_eq!(nixos.stubs, vec!["@nixos"]);

        let home = &config.context["home"];
        assert_eq!(home.paths, vec!["home/**/*.nix"]);
        assert_eq!(home.stubs, vec!["@home-manager", "./stubs/home.tix"]);
    }

    #[test]
    fn parse_empty_config() {
        let config: TixConfig = toml::from_str("").expect("parse error");
        assert!(config.stubs.is_empty());
        assert!(config.context.is_empty());
    }
}
