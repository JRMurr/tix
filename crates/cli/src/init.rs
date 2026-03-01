// ==============================================================================
// `tix init` — Scaffold a tix.toml from project structure
// ==============================================================================
//
// Scans a project directory for .nix files, classifies each one using the
// AST-level classifier (lang_ast::classify), groups by kind and directory,
// and generates a tix.toml configuration file.

use std::collections::HashMap;
use std::error::Error;
use std::path::{Path, PathBuf};

use lang_ast::classify::{classify_nix_file, Classification, NixFileKind};
use lang_ast::{module, name_resolution, NixFile, RootDatabase};

use crate::config::{self, TixConfig};

/// Entry point for `tix init`.
pub fn run_init(path: PathBuf, yes: bool, dry_run: bool) -> Result<(), Box<dyn Error>> {
    // Step 1: Find project root (walk up for flake.nix or .git, fallback to cwd).
    let project_root = find_project_root(&path);
    let toml_path = project_root.join("tix.toml");

    // Step 2: Check if tix.toml already exists.
    if toml_path.exists() && !yes {
        return Err(format!(
            "{} already exists. Use --yes to overwrite.",
            toml_path.display()
        )
        .into());
    }

    // Step 3: Discover all .nix files.
    let empty_config = TixConfig::default();
    let nix_files = config::discover_all_nix_files(&project_root, &empty_config);

    if nix_files.is_empty() {
        eprintln!("No .nix files found in {}", project_root.display());
        return Ok(());
    }

    eprintln!("Scanning {}...", project_root.display());

    // Step 4: Parse + classify each file.
    let db = RootDatabase::default();
    let mut classifications: Vec<(PathBuf, Classification)> = Vec::new();

    for file_path in &nix_files {
        let relative = file_path
            .strip_prefix(&project_root)
            .unwrap_or(file_path)
            .to_path_buf();

        match classify_file(&db, file_path) {
            Some(c) => classifications.push((relative, c)),
            None => {
                eprintln!("  warning: failed to parse {}", relative.display());
            }
        }
    }

    // Step 5: Group by NixFileKind.
    let mut by_kind: HashMap<NixFileKind, Vec<(PathBuf, Classification)>> = HashMap::new();
    for (path, classification) in &classifications {
        by_kind
            .entry(classification.kind)
            .or_default()
            .push((path.clone(), classification.clone()));
    }

    // Step 6: Print summary.
    eprintln!("Found {} .nix files:", nix_files.len());
    let kind_order = [
        NixFileKind::NixosModule,
        NixFileKind::HomeManagerModule,
        NixFileKind::CallPackage,
        NixFileKind::Overlay,
        NixFileKind::Library,
        NixFileKind::Flake,
        NixFileKind::PlainExpression,
    ];
    for kind in &kind_order {
        if let Some(files) = by_kind.get(kind) {
            let dirs = collect_unique_dirs(files);
            let dir_str = if dirs.is_empty() {
                String::new()
            } else {
                format!("  ({})", dirs.join(", "))
            };
            eprintln!("  {:24}{:>3}{}", format!("{}:", kind), files.len(), dir_str);
        }
    }

    // Step 7: Generate tix.toml content.
    let toml_content = generate_toml(&by_kind, &project_root);

    // Step 8: Write or print.
    if dry_run {
        println!("{toml_content}");
    } else {
        std::fs::write(&toml_path, &toml_content)?;
        eprintln!("\nWrote {}", toml_path.display());
    }

    Ok(())
}

// ==============================================================================
// Helpers
// ==============================================================================

/// Classify a single file, returning None if parsing fails.
fn classify_file(db: &RootDatabase, file_path: &Path) -> Option<Classification> {
    let contents = std::fs::read_to_string(file_path).ok()?;
    let nix_file = NixFile::new(db, file_path.to_path_buf(), contents);
    let m = module(db, nix_file);
    let nr = name_resolution(db, nix_file);
    Some(classify_nix_file(&m, &nr))
}

/// Find the project root by walking up from `start` looking for flake.nix or .git.
fn find_project_root(start: &Path) -> PathBuf {
    let start = std::fs::canonicalize(start).unwrap_or_else(|_| start.to_path_buf());
    let start = if start.is_file() {
        start.parent().unwrap_or(&start).to_path_buf()
    } else {
        start
    };

    let mut dir = start.as_path();
    loop {
        if dir.join("flake.nix").exists() || dir.join(".git").exists() {
            return dir.to_path_buf();
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => return start,
        }
    }
}

/// Collect unique parent directories from a list of classified files.
fn collect_unique_dirs(files: &[(PathBuf, Classification)]) -> Vec<String> {
    let mut dirs: Vec<String> = files
        .iter()
        .filter_map(|(p, _)| {
            p.parent()
                .filter(|d| !d.as_os_str().is_empty())
                .map(|d| d.display().to_string())
        })
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    dirs.sort();
    dirs
}

/// Derive glob patterns from a list of files grouped by kind.
/// If all files in a directory share the same kind, use `dir/**/*.nix`.
/// Otherwise, list individual paths.
fn derive_glob_patterns(files: &[(PathBuf, Classification)]) -> Vec<String> {
    // Group by parent directory.
    let mut by_dir: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
    for (path, _) in files {
        let dir = path.parent().unwrap_or(Path::new(".")).to_path_buf();
        by_dir.entry(dir).or_default().push(path.clone());
    }

    let mut patterns = Vec::new();
    for (dir, dir_files) in &by_dir {
        if dir.as_os_str().is_empty() || dir == Path::new(".") {
            // Root-level files: list individually.
            for f in dir_files {
                patterns.push(f.display().to_string());
            }
        } else if dir_files.len() >= 2 {
            // Multiple files in same dir: use glob.
            patterns.push(format!("{}/**/*.nix", dir.display()));
        } else {
            // Single file in dir: list it.
            for f in dir_files {
                patterns.push(f.display().to_string());
            }
        }
    }

    patterns.sort();
    patterns.dedup();
    patterns
}

/// Generate the tix.toml content from classified files.
fn generate_toml(
    by_kind: &HashMap<NixFileKind, Vec<(PathBuf, Classification)>>,
    _project_root: &Path,
) -> String {
    let mut sections = Vec::new();

    // Header comment.
    sections.push("# tix.toml — generated by `tix init`\n".to_string());

    // NixOS modules context.
    if let Some(files) = by_kind.get(&NixFileKind::NixosModule) {
        let patterns = derive_glob_patterns(files);
        if !patterns.is_empty() {
            sections.push(format!(
                "[context.nixos]\npaths = [{}]\nstubs = [\"@nixos\"]\n",
                format_string_array(&patterns),
            ));
        }
    }

    // Home Manager modules context.
    if let Some(files) = by_kind.get(&NixFileKind::HomeManagerModule) {
        let patterns = derive_glob_patterns(files);
        if !patterns.is_empty() {
            sections.push(format!(
                "[context.home-manager]\npaths = [{}]\nstubs = [\"@home-manager\"]\n",
                format_string_array(&patterns),
            ));
        }
    }

    // callPackage context.
    if let Some(files) = by_kind.get(&NixFileKind::CallPackage) {
        let patterns = derive_glob_patterns(files);
        if !patterns.is_empty() {
            sections.push(format!(
                "[context.callpackage]\npaths = [{}]\nstubs = [\"@callpackage\"]\n",
                format_string_array(&patterns),
            ));
        }
    }

    // Overlay / Library / Plain files — commented out as informational.
    for (kind, label) in [
        (NixFileKind::Overlay, "overlay"),
        (NixFileKind::Library, "library"),
        (NixFileKind::Flake, "flake"),
    ] {
        if let Some(files) = by_kind.get(&kind) {
            let patterns = derive_glob_patterns(files);
            if !patterns.is_empty() {
                sections.push(format!(
                    "# {label} files (no context needed): {}\n",
                    patterns.join(", ")
                ));
            }
        }
    }

    // Project section with exclude defaults.
    sections.push("[project]\nexclude = [\"result\", \".direnv\"]\n".to_string());

    sections.join("\n")
}

/// Format a list of strings as a TOML inline array.
fn format_string_array(items: &[String]) -> String {
    items
        .iter()
        .map(|s| format!("\"{s}\""))
        .collect::<Vec<_>>()
        .join(", ")
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_project_root_with_flake() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::write(root.join("flake.nix"), "{}").unwrap();
        std::fs::create_dir_all(root.join("modules/sub")).unwrap();

        let found = find_project_root(&root.join("modules/sub"));
        assert_eq!(found, std::fs::canonicalize(root).unwrap());
    }

    #[test]
    fn find_project_root_with_git() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::create_dir_all(root.join("src")).unwrap();

        let found = find_project_root(&root.join("src"));
        assert_eq!(found, std::fs::canonicalize(root).unwrap());
    }

    #[test]
    fn derive_globs_groups_by_directory() {
        let files = vec![
            (PathBuf::from("modules/a.nix"), dummy_classification()),
            (PathBuf::from("modules/b.nix"), dummy_classification()),
        ];
        let patterns = derive_glob_patterns(&files);
        assert_eq!(patterns, vec!["modules/**/*.nix"]);
    }

    #[test]
    fn derive_globs_single_file_listed() {
        let files = vec![(PathBuf::from("pkgs/foo.nix"), dummy_classification())];
        let patterns = derive_glob_patterns(&files);
        assert_eq!(patterns, vec!["pkgs/foo.nix"]);
    }

    #[test]
    fn init_dry_run_generates_toml() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();

        // Create a NixOS-looking module.
        std::fs::create_dir_all(root.join("modules")).unwrap();
        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::write(
            root.join("modules/foo.nix"),
            "{ config, lib, pkgs, ... }: { options.x = lib.mkOption {}; }",
        )
        .unwrap();

        // Create a callPackage file.
        std::fs::create_dir_all(root.join("pkgs")).unwrap();
        std::fs::write(
            root.join("pkgs/bar.nix"),
            "{ stdenv, fetchFromGitHub, ... }: stdenv.mkDerivation { pname = \"bar\"; }",
        )
        .unwrap();

        let result = run_init(root.to_path_buf(), false, true);
        assert!(result.is_ok(), "init --dry-run failed: {:?}", result.err());
    }

    #[test]
    fn init_errors_if_toml_exists() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::write(root.join("tix.toml"), "# existing").unwrap();

        let result = run_init(root.to_path_buf(), false, false);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("already exists"));
    }

    fn dummy_classification() -> Classification {
        Classification {
            kind: NixFileKind::NixosModule,
            confidence: 0.8,
            explicit_context: None,
            reason: "test".into(),
        }
    }
}
