// ==============================================================================
// tix.toml Project Configuration (for LSP)
// ==============================================================================
//
// Mirrors the CLI's config module for discovering and loading `tix.toml` files.
// Provides per-file context resolution for NixOS/Home Manager module typing.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use comment_parser::ParsedTy;
use lang_check::aliases::TypeAliasRegistry;
use serde::Deserialize;
use smol_str::SmolStr;

/// Top-level `tix.toml` configuration.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct ProjectConfig {
    /// Stub configuration: either a plain array of paths (`stubs = ["./stubs"]`)
    /// or a table with `paths` and/or `generate` keys.
    #[serde(default)]
    pub stubs: StubsConfig,

    /// Named contexts mapping file globs to module arg types.
    #[serde(default)]
    pub context: HashMap<String, ContextConfig>,

    /// Project-wide analysis configuration.
    #[serde(default)]
    pub project: Option<ProjectSection>,

    /// Diagnostic severity overrides.
    #[serde(default)]
    pub diagnostics: Option<DiagnosticsProjectConfig>,
}

// ==============================================================================
// Stubs Configuration
// ==============================================================================

/// The `stubs` field in tix.toml supports two formats:
///
/// 1. Array of paths (backward-compatible):
///    ```toml
///    stubs = ["./my-stubs/"]
///    ```
///
/// 2. Table with optional `paths` and `generate` keys:
///    ```toml
///    [stubs]
///    paths = ["./my-stubs/"]
///    [stubs.generate]
///    nixpkgs = "/nix/store/...-nixpkgs-src"
///    ```
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum StubsConfig {
    Paths(Vec<String>),
    Table {
        #[serde(default)]
        paths: Vec<String>,
        #[serde(default)]
        generate: Option<StubsGenerateConfig>,
    },
}

impl Default for StubsConfig {
    fn default() -> Self {
        StubsConfig::Paths(Vec::new())
    }
}

impl StubsConfig {
    /// Get the list of stub file/directory paths.
    pub fn paths(&self) -> &[String] {
        match self {
            StubsConfig::Paths(paths) => paths,
            StubsConfig::Table { paths, .. } => paths,
        }
    }

    /// Get the runtime generation config, if configured.
    pub fn generate(&self) -> Option<&StubsGenerateConfig> {
        match self {
            StubsConfig::Paths(_) => None,
            StubsConfig::Table { generate, .. } => generate.as_ref(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.paths().is_empty() && self.generate().is_none()
    }
}

/// A Nix source reference: either a direct store path or a Nix expression
/// that evaluates to one.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum NixSource {
    Path(String),
    Expr { expr: String },
}

/// Configuration for runtime stub generation via Nix.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct StubsGenerateConfig {
    pub nixpkgs: Option<NixSource>,
    #[serde(default, rename = "home-manager")]
    pub home_manager: Option<NixSource>,
}

/// The `[diagnostics]` section of `tix.toml`.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct DiagnosticsProjectConfig {
    /// Severity for unknown-type (`?`) diagnostics: "off", "hint", "warning", "error".
    #[serde(default)]
    pub unknown_type: Option<crate::config::DiagnosticLevel>,
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

    /// Glob patterns for files/directories to exclude from `tix check`.
    /// Example: `exclude = ["result", "vendor/**"]`
    #[serde(default)]
    pub exclude: Vec<String>,
}

/// A single context definition within `tix.toml`.
#[derive(Debug, Clone, Deserialize)]
pub struct ContextConfig {
    /// Glob patterns for files this context applies to.
    pub paths: Vec<String>,

    /// Glob patterns for files to exclude even if `paths` matches.
    #[serde(default)]
    pub exclude: Vec<String>,

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
/// stubs (returned as `Arc` for cheap sharing); all others are treated as
/// file/directory paths relative to `config_dir`.
fn load_stub_entry(
    entry: &str,
    config_dir: &Path,
    registry: &mut TypeAliasRegistry,
) -> Result<Arc<HashMap<SmolStr, ParsedTy>>, Box<dyn std::error::Error>> {
    if let Some(builtin_name) = entry.strip_prefix('@') {
        registry
            .load_context_by_name(builtin_name)
            .ok_or_else(|| format!("Unknown built-in context: @{builtin_name}"))?
    } else {
        let path = config_dir.join(entry);
        let source = std::fs::read_to_string(&path)
            .map_err(|e| format!("Failed to read {}: {e}", path.display()))?;
        registry.load_context_stubs(&source).map(Arc::new)
    }
}

/// Resolve context args for a file based on `tix.toml` context definitions.
///
/// When a context has a single stub entry, the returned `Arc` shares the
/// cached allocation from the registry — no deep clone of potentially large
/// context maps (e.g. 24K entries for pkgs.tix).
pub fn resolve_context_for_file(
    file_path: &Path,
    config: &ProjectConfig,
    config_dir: &Path,
    registry: &mut TypeAliasRegistry,
) -> Result<Arc<HashMap<SmolStr, ParsedTy>>, Box<dyn std::error::Error>> {
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

        let excluded = matched
            && ctx.exclude.iter().any(|pattern| {
                globset::GlobBuilder::new(pattern)
                    .literal_separator(true)
                    .build()
                    .ok()
                    .and_then(|g| g.compile_matcher().is_match(relative).then_some(()))
                    .is_some()
            });

        if matched && !excluded {
            // Fast path: single stub entry — return the Arc directly without
            // allocating a merge HashMap.
            if ctx.stubs.len() == 1 {
                return load_stub_entry(&ctx.stubs[0], config_dir, registry);
            }

            // Multi-stub: merge all entries into a new HashMap.
            let mut merged = HashMap::new();
            for stub_entry in &ctx.stubs {
                match load_stub_entry(stub_entry, config_dir, registry) {
                    Ok(args) => merged.extend(args.iter().map(|(k, v)| (k.clone(), v.clone()))),
                    Err(e) => log::warn!("Failed to load context stub '{stub_entry}': {e}"),
                }
            }
            return Ok(Arc::new(merged));
        }
    }

    Ok(Arc::default())
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
/// Note: `walk_dir_matching` does not follow directory symlinks recursively
/// (it uses `read_dir` which lists entries without following symlinks for
/// directories). This is intentional to avoid potential infinite loops from
/// circular symlinks.
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
            if glob_set.is_match(relative) {
                // Canonicalize so background-queue paths match uri_to_path()
                // (which also canonicalizes). Without this, symlinked dirs
                // like /etc/nixos → /home/user/config produce different URIs
                // for background vs user-triggered analysis, causing stale
                // diagnostics that are never cleared.
                let canonical = path.canonicalize().unwrap_or(path);
                if seen.insert(canonical.clone()) {
                    out.push(canonical);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config_with_analyze(patterns: Vec<&str>) -> ProjectConfig {
        ProjectConfig {
            project: Some(ProjectSection {
                analyze: patterns.into_iter().map(String::from).collect(),
                ..Default::default()
            }),
            ..Default::default()
        }
    }

    #[test]
    fn empty_analyze_returns_empty() {
        let config = ProjectConfig::default();
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_analyze_globs(&config, dir.path());
        assert!(result.is_empty());
    }

    #[test]
    fn single_glob_matches_files() {
        let dir = tempfile::tempdir().unwrap();
        let lib_dir = dir.path().join("lib");
        std::fs::create_dir(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("strings.nix"), "42").unwrap();
        std::fs::write(lib_dir.join("lists.nix"), "42").unwrap();
        // Non-.nix file should not match.
        std::fs::write(lib_dir.join("README.md"), "hello").unwrap();

        let config = config_with_analyze(vec!["lib/*.nix"]);
        let result = resolve_analyze_globs(&config, dir.path());
        assert_eq!(result.len(), 2, "should match both .nix files");
    }

    #[test]
    fn single_glob_does_not_cross_directories() {
        let dir = tempfile::tempdir().unwrap();
        let lib_dir = dir.path().join("lib");
        let sub_dir = lib_dir.join("sub");
        std::fs::create_dir_all(&sub_dir).unwrap();
        std::fs::write(lib_dir.join("top.nix"), "42").unwrap();
        std::fs::write(sub_dir.join("deep.nix"), "42").unwrap();

        // lib/*.nix should NOT match lib/sub/deep.nix.
        let config = config_with_analyze(vec!["lib/*.nix"]);
        let result = resolve_analyze_globs(&config, dir.path());
        assert_eq!(result.len(), 1, "should only match top-level lib/ files");
        assert!(result[0].ends_with("top.nix"));
    }

    #[test]
    fn double_star_matches_deep_files() {
        let dir = tempfile::tempdir().unwrap();
        let lib_dir = dir.path().join("lib");
        let sub_dir = lib_dir.join("sub");
        std::fs::create_dir_all(&sub_dir).unwrap();
        std::fs::write(lib_dir.join("top.nix"), "42").unwrap();
        std::fs::write(sub_dir.join("deep.nix"), "42").unwrap();

        let config = config_with_analyze(vec!["lib/**/*.nix"]);
        let result = resolve_analyze_globs(&config, dir.path());
        assert_eq!(result.len(), 2, "** should match files at any depth");
    }

    #[test]
    fn invalid_pattern_is_skipped() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("test.nix"), "42").unwrap();

        // An invalid glob pattern should be skipped (logged as warning),
        // not crash.
        let config = config_with_analyze(vec!["[invalid"]);
        let result = resolve_analyze_globs(&config, dir.path());
        assert!(
            result.is_empty(),
            "invalid pattern should not match anything"
        );
    }

    #[test]
    fn context_exclude_defaults_to_empty() {
        let toml_str = r#"
            [context.nixos]
            paths = ["modules/**/*.nix"]
            stubs = ["@nixos"]
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        assert!(config.context["nixos"].exclude.is_empty());
    }

    #[test]
    fn context_exclude_parses_when_present() {
        let toml_str = r#"
            [context.nixos]
            paths = ["common/**/*.nix", "hosts/**/*.nix"]
            exclude = ["common/homemanager/**/*.nix", "common/default.nix"]
            stubs = ["@nixos"]
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(
            config.context["nixos"].exclude,
            vec!["common/homemanager/**/*.nix", "common/default.nix"]
        );
    }

    #[test]
    fn resolve_context_respects_exclude() {
        let toml_str = r#"
            [context.nixos]
            paths = ["common/**/*.nix"]
            exclude = ["common/homemanager/**/*.nix"]
            stubs = ["@nixos"]

            [context.home]
            paths = ["common/homemanager/**/*.nix"]
            stubs = ["@home-manager"]
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        let mut registry = lang_check::aliases::TypeAliasRegistry::with_builtins();

        // A file in common/ should match nixos context.
        let direct = Path::new("common/programs.nix");
        let args = resolve_context_for_file(direct, &config, Path::new("."), &mut registry)
            .expect("resolve error");
        assert!(
            args.contains_key("modulesPath"),
            "common/programs.nix should match nixos context, got keys: {:?}",
            args.keys().collect::<Vec<_>>()
        );

        // A file in common/homemanager/ should NOT match nixos (excluded),
        // but should fall through to the home-manager context.
        let nested = Path::new("common/homemanager/default.nix");
        let args = resolve_context_for_file(nested, &config, Path::new("."), &mut registry)
            .expect("resolve error");
        assert!(
            args.contains_key("osConfig"),
            "common/homemanager/default.nix should match home-manager context (has osConfig), got keys: {:?}",
            args.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn diagnostics_section_parses() {
        let toml_str = r#"
            [diagnostics]
            unknown_type = "warning"
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        let diag = config
            .diagnostics
            .expect("diagnostics section should exist");
        assert_eq!(
            diag.unknown_type,
            Some(crate::config::DiagnosticLevel::Warning)
        );
    }

    #[test]
    fn diagnostics_section_defaults_to_none() {
        let config: ProjectConfig = toml::from_str("").expect("parse error");
        assert!(config.diagnostics.is_none());
    }

    /// Regression test: symlinked directories should produce canonical paths
    /// so that background analysis diagnostics match uri_to_path() paths.
    /// Without canonicalization, stale timeout diagnostics persist because
    /// the editor sees two different URIs for the same file.
    #[cfg(unix)]
    #[test]
    fn symlinked_dir_returns_canonical_paths() {
        let dir = tempfile::tempdir().unwrap();
        // Create actual directory with a .nix file.
        let real_dir = dir.path().join("real");
        std::fs::create_dir(&real_dir).unwrap();
        std::fs::write(real_dir.join("config.nix"), "42").unwrap();
        // Create a symlink pointing to the real directory.
        let link = dir.path().join("link");
        std::os::unix::fs::symlink(&real_dir, &link).unwrap();

        let config = config_with_analyze(vec!["*.nix"]);
        // Resolve starting from the symlink path.
        let result = resolve_analyze_globs(&config, &link);
        assert_eq!(result.len(), 1);
        // The returned path should be canonical (through real_dir, not link).
        let canonical_real = real_dir.canonicalize().unwrap();
        assert_eq!(
            result[0],
            canonical_real.join("config.nix"),
            "paths should be canonicalized to match uri_to_path()"
        );
    }

    #[test]
    fn diagnostics_section_off() {
        let toml_str = r#"
            [diagnostics]
            unknown_type = "off"
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        let diag = config
            .diagnostics
            .expect("diagnostics section should exist");
        assert_eq!(diag.unknown_type, Some(crate::config::DiagnosticLevel::Off));
    }

    // =========================================================================
    // StubsConfig parsing tests
    // =========================================================================

    #[test]
    fn stubs_array_backward_compat() {
        let toml_str = r#"stubs = ["./stubs", "./extra.tix"]"#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(config.stubs.paths(), &["./stubs", "./extra.tix"]);
        assert!(config.stubs.generate().is_none());
    }

    #[test]
    fn stubs_table_with_paths_and_generate() {
        let toml_str = r#"
            [stubs]
            paths = ["./my-stubs/"]

            [stubs.generate]
            nixpkgs = "/nix/store/abc-nixpkgs-src"
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(config.stubs.paths(), &["./my-stubs/"]);
        let gen = config.stubs.generate().expect("generate should be present");
        assert!(
            matches!(&gen.nixpkgs, Some(NixSource::Path(p)) if p == "/nix/store/abc-nixpkgs-src")
        );
        assert!(gen.home_manager.is_none());
    }

    #[test]
    fn stubs_generate_with_expr() {
        let toml_str = r#"
            [stubs.generate]
            nixpkgs = { expr = "(builtins.getFlake (toString ./.)).inputs.nixpkgs" }
            home-manager = { expr = "(builtins.getFlake (toString ./.)).inputs.home-manager" }
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        assert!(config.stubs.paths().is_empty());
        let gen = config.stubs.generate().expect("generate should be present");
        assert!(
            matches!(&gen.nixpkgs, Some(NixSource::Expr { expr }) if expr.contains("getFlake"))
        );
        assert!(
            matches!(&gen.home_manager, Some(NixSource::Expr { expr }) if expr.contains("home-manager"))
        );
    }

    #[test]
    fn stubs_generate_only_nixpkgs() {
        let toml_str = r#"
            [stubs.generate]
            nixpkgs = "/nix/store/abc-nixpkgs-src"
        "#;
        let config: ProjectConfig = toml::from_str(toml_str).expect("parse error");
        let gen = config.stubs.generate().expect("generate should be present");
        assert!(gen.nixpkgs.is_some());
        assert!(gen.home_manager.is_none());
    }

    #[test]
    fn stubs_empty_default() {
        let config: ProjectConfig = toml::from_str("").expect("parse error");
        assert!(config.stubs.paths().is_empty());
        assert!(config.stubs.generate().is_none());
        assert!(config.stubs.is_empty());
    }
}
