// ==============================================================================
// tix.toml Configuration
// ==============================================================================
//
// Re-exports shared tix.toml types from `tix_lsp::project_config` and adds
// CLI-specific file discovery logic (used by `tix check`).
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

use std::path::{Path, PathBuf};

// Re-export shared types so the rest of the CLI can use `config::TixConfig`, etc.
pub use tix_lsp::project_config::{find_config, load_config, resolve_context_for_file};

/// Type alias: the CLI historically called this `TixConfig` while the LSP
/// uses `ProjectConfig`. Same struct — tix.toml representation.
pub type TixConfig = tix_lsp::project_config::ProjectConfig;

// ==============================================================================
// File Discovery
// ==============================================================================

/// Hardcoded directory names to always skip during recursive walks.
const SKIP_DIRS: &[&str] = &[".git", "node_modules", "result", ".direnv", "target"];

/// Discover all `.nix` files under `root`, respecting exclude patterns from
/// the `[project]` section and hardcoded ignores.
pub fn discover_all_nix_files(root: &Path, config: &TixConfig) -> Vec<PathBuf> {
    let exclude_set = build_exclude_set(config);
    let mut paths = Vec::new();
    let mut seen = std::collections::HashSet::new();
    walk_nix_files(root, root, &exclude_set, &mut seen, &mut paths);
    paths.sort();
    paths
}

/// Build a GlobSet from the `[project] exclude` patterns.
fn build_exclude_set(config: &TixConfig) -> Option<globset::GlobSet> {
    let patterns: Vec<&str> = config
        .project
        .as_ref()
        .map(|p| p.exclude.iter().map(|s| s.as_str()).collect())
        .unwrap_or_default();

    if patterns.is_empty() {
        return None;
    }

    let mut builder = globset::GlobSetBuilder::new();
    for pattern in patterns {
        if let Ok(glob) = globset::GlobBuilder::new(pattern)
            .literal_separator(true)
            .build()
        {
            builder.add(glob);
        }
    }
    builder.build().ok()
}

/// Recursively walk `dir`, collecting `.nix` files.
fn walk_nix_files(
    dir: &Path,
    root: &Path,
    exclude_set: &Option<globset::GlobSet>,
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
            // Skip hardcoded directories.
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if SKIP_DIRS.contains(&name) {
                    continue;
                }
            }
            // Skip excluded directories.
            if let Some(ref gs) = exclude_set {
                let relative = path.strip_prefix(root).unwrap_or(&path);
                if gs.is_match(relative) {
                    continue;
                }
            }
            walk_nix_files(&path, root, exclude_set, seen, out);
        } else if path.is_file() && path.extension().is_some_and(|e| e == "nix") {
            // Check file-level exclude patterns.
            if let Some(ref gs) = exclude_set {
                let relative = path.strip_prefix(root).unwrap_or(&path);
                if gs.is_match(relative) {
                    continue;
                }
            }
            if seen.insert(path.clone()) {
                out.push(path);
            }
        }
    }
}

/// Check if a file path matches any context in the config.
/// Returns the context name if matched, or None.
pub fn find_matching_context<'a>(
    file_path: &Path,
    config: &'a TixConfig,
    config_dir: &Path,
) -> Option<&'a str> {
    let relative = file_path.strip_prefix(config_dir).unwrap_or(file_path);

    for (name, ctx) in &config.context {
        let matched = ctx.paths.iter().any(|pattern| {
            globset::GlobBuilder::new(pattern)
                .literal_separator(true)
                .build()
                .ok()
                .and_then(|g| g.compile_matcher().is_match(relative).then_some(()))
                .is_some()
        });
        if matched {
            return Some(name.as_str());
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_check::aliases::TypeAliasRegistry;

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

    #[test]
    fn parse_config_with_project_section() {
        let toml_str = r#"
            stubs = ["./stubs"]
            deadline = 30

            [project]
            analyze = ["lib/*.nix"]
            exclude = ["vendor/**", "result"]

            [context.nixos]
            paths = ["modules/**/*.nix"]
            stubs = ["@nixos"]
        "#;
        let config: TixConfig = toml::from_str(toml_str).expect("parse error");
        assert_eq!(config.deadline, Some(30));
        let project = config.project.as_ref().unwrap();
        assert_eq!(project.analyze, vec!["lib/*.nix"]);
        assert_eq!(project.exclude, vec!["vendor/**", "result"]);
    }

    #[test]
    fn discover_nix_files_respects_excludes() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let root = dir.path();

        // Create directory structure.
        std::fs::create_dir_all(root.join("modules")).unwrap();
        std::fs::create_dir_all(root.join("vendor/dep")).unwrap();
        std::fs::write(root.join("modules/foo.nix"), "42").unwrap();
        std::fs::write(root.join("vendor/dep/bar.nix"), "42").unwrap();
        std::fs::write(root.join("top.nix"), "42").unwrap();

        let config: TixConfig = toml::from_str(
            r#"
            [project]
            exclude = ["vendor/**"]
            "#,
        )
        .unwrap();

        let files = discover_all_nix_files(root, &config);
        let names: Vec<_> = files.iter().map(|p| p.file_name().unwrap()).collect();
        assert!(names.contains(&std::ffi::OsStr::new("foo.nix")));
        assert!(names.contains(&std::ffi::OsStr::new("top.nix")));
        assert!(
            !names.contains(&std::ffi::OsStr::new("bar.nix")),
            "vendor files should be excluded"
        );
    }

    #[test]
    fn discover_skips_hardcoded_dirs() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let root = dir.path();

        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::create_dir_all(root.join("node_modules")).unwrap();
        std::fs::write(root.join(".git/config.nix"), "42").unwrap();
        std::fs::write(root.join("node_modules/pkg.nix"), "42").unwrap();
        std::fs::write(root.join("top.nix"), "42").unwrap();

        let config = TixConfig::default();
        let files = discover_all_nix_files(root, &config);
        assert_eq!(files.len(), 1);
        assert!(files[0].ends_with("top.nix"));
    }

    // Regression: `common/*.nix` was matching `common/homemanager/default.nix`
    // because globset defaults to `literal_separator: false`, allowing `*` to
    // cross `/` boundaries. This caused files in subdirectories to match a
    // parent-only glob, picking up the wrong context stubs.
    #[test]
    fn star_glob_does_not_cross_path_separators() {
        let config: TixConfig = toml::from_str(
            r#"
            [context.nixos]
            paths = ["common/*.nix"]
            stubs = ["@nixos"]

            [context.home]
            paths = ["common/homemanager/**/*.nix"]
            stubs = ["@home-manager"]
            "#,
        )
        .expect("parse error");

        let mut registry = TypeAliasRegistry::with_builtins();

        // A file directly in common/ should match the nixos context.
        let direct = Path::new("common/programs.nix");
        let args = resolve_context_for_file(direct, &config, Path::new("."), &mut registry)
            .expect("resolve error");
        assert!(
            args.contains_key("modulesPath"),
            "common/programs.nix should match nixos context (has modulesPath), got keys: {:?}",
            args.keys().collect::<Vec<_>>()
        );

        // A file in a subdirectory should NOT match `common/*.nix` — it should
        // fall through to the `common/homemanager/**/*.nix` glob instead.
        let nested = Path::new("common/homemanager/default.nix");
        let args = resolve_context_for_file(nested, &config, Path::new("."), &mut registry)
            .expect("resolve error");
        assert!(
            args.contains_key("osConfig"),
            "common/homemanager/default.nix should match home-manager context (has osConfig), got keys: {:?}",
            args.keys().collect::<Vec<_>>()
        );
    }
}
