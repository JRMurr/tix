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

/// Result of `derive_glob_patterns`: inclusion patterns + exclusion patterns.
#[derive(Debug, PartialEq, Eq)]
struct GlobResult {
    paths: Vec<String>,
    excludes: Vec<String>,
}

/// Derive glob patterns from a list of files of one kind.
///
/// `all_files` contains every classified file across all kinds — used to detect
/// mixed-kind directories where a recursive `dir/**/*.nix` glob would be wrong
/// (it would match files belonging to other kinds).
///
/// Rules:
/// - Only emit `dir/**/*.nix` when 2+ files share a parent AND no file from
///   another kind exists anywhere under `dir/`.
/// - For mixed directories, try glob + exclude patterns if that's more concise
///   than listing every this-kind file individually.
/// - After generating patterns, remove any subsumed by a parent glob.
fn derive_glob_patterns(
    files: &[(PathBuf, Classification)],
    all_files: &[(PathBuf, Classification)],
) -> GlobResult {
    let this_kind = files.first().map(|(_, c)| c.kind);

    // Paths from other kinds, used for conflict detection.
    let other_kind_paths: Vec<&Path> = all_files
        .iter()
        .filter(|(_, c)| Some(c.kind) != this_kind)
        .map(|(p, _)| p.as_path())
        .collect();

    // This-kind paths as a set, for checking subdir purity in compress_excludes.
    let this_kind_set: std::collections::HashSet<&Path> =
        files.iter().map(|(p, _)| p.as_path()).collect();

    // Group by parent directory.
    let mut by_dir: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
    for (path, _) in files {
        let dir = path.parent().unwrap_or(Path::new(".")).to_path_buf();
        by_dir.entry(dir).or_default().push(path.clone());
    }

    let mut patterns = Vec::new();
    let mut excludes = Vec::new();

    for (dir, dir_files) in &by_dir {
        if dir.as_os_str().is_empty() || dir == Path::new(".") {
            for f in dir_files {
                patterns.push(f.display().to_string());
            }
        } else if dir_files.len() >= 2 {
            // Check whether any file from another kind lives under this directory.
            let dir_prefix = format!("{}/", dir.display());
            let other_files_under_dir: Vec<&Path> = other_kind_paths
                .iter()
                .filter(|p| p.to_str().is_some_and(|s| s.starts_with(&dir_prefix)))
                .copied()
                .collect();

            if other_files_under_dir.is_empty() {
                // Pure directory — safe to use recursive glob.
                patterns.push(format!("{}/**/*.nix", dir.display()));
            } else {
                // Mixed directory: try glob + exclude if more concise.
                let dir_excludes = compress_excludes(&other_files_under_dir, &this_kind_set, dir);
                let this_kind_count = dir_files.len();

                // Conciseness heuristic: glob + excludes wins when
                // 1 (the glob) + |excludes| < |this_kind_files|.
                if 1 + dir_excludes.len() < this_kind_count {
                    patterns.push(format!("{}/**/*.nix", dir.display()));
                    excludes.extend(dir_excludes);
                } else {
                    for f in dir_files {
                        patterns.push(f.display().to_string());
                    }
                }
            }
        } else {
            for f in dir_files {
                patterns.push(f.display().to_string());
            }
        }
    }

    patterns.sort();
    patterns.dedup();
    excludes.sort();
    excludes.dedup();

    // Collect the directory prefixes that have recursive globs.
    let glob_dirs: Vec<String> = patterns
        .iter()
        .filter_map(|p| p.strip_suffix("/**/*.nix").map(|d| d.to_string()))
        .collect();

    // Remove any pattern whose path falls under an existing recursive glob.
    // This handles both individual files (e.g. `dir/sub/foo.nix` under `dir/**/*.nix`)
    // and child globs (e.g. `dir/sub/**/*.nix` under `dir/**/*.nix`).
    patterns.retain(|pattern| {
        let pattern_dir = if let Some(dir) = pattern.strip_suffix("/**/*.nix") {
            dir
        } else if let Some(parent) = Path::new(pattern).parent() {
            parent.to_str().unwrap_or("")
        } else {
            return true;
        };

        !glob_dirs.iter().any(|glob_dir| {
            pattern_dir != glob_dir.as_str() && pattern_dir.starts_with(&format!("{glob_dir}/"))
        })
    });

    GlobResult {
        paths: patterns,
        excludes,
    }
}

/// Compress a set of other-kind files into exclude patterns.
///
/// Groups files by their parent directory. When 2+ other-kind files share a
/// subdirectory AND no this-kind files exist under that subdirectory, emit a
/// single `subdir/**/*.nix` exclude glob. Otherwise, list individual files.
fn compress_excludes(
    other_files: &[&Path],
    this_kind_set: &std::collections::HashSet<&Path>,
    parent_dir: &Path,
) -> Vec<String> {
    // Group other-kind files by their immediate parent directory.
    let mut by_subdir: HashMap<PathBuf, Vec<&Path>> = HashMap::new();
    for &file in other_files {
        let file_parent = file.parent().unwrap_or(Path::new(".")).to_path_buf();
        by_subdir.entry(file_parent).or_default().push(file);
    }

    let mut excludes = Vec::new();
    let mut subsumed: std::collections::HashSet<&Path> = std::collections::HashSet::new();

    // First pass: identify subdirectories that can be glob-excluded.
    for (subdir, subdir_files) in &by_subdir {
        // Only compress to a subdir glob if it's a proper subdirectory (not parent_dir itself)
        // and has 2+ files.
        if subdir == parent_dir || subdir_files.len() < 2 {
            continue;
        }

        // Check that no this-kind files exist under this subdirectory.
        let subdir_prefix = format!("{}/", subdir.display());
        let has_this_kind_in_subdir = this_kind_set.iter().any(|p| {
            p.to_str()
                .is_some_and(|s| s.starts_with(&subdir_prefix) || *p == subdir.as_path())
        });

        if !has_this_kind_in_subdir {
            excludes.push(format!("{}/**/*.nix", subdir.display()));
            // Mark these files as subsumed so we don't list them individually.
            for &f in subdir_files {
                subsumed.insert(f);
            }
        }
    }

    // Second pass: list remaining files individually.
    for &file in other_files {
        if subsumed.contains(file) {
            continue;
        }
        // Also skip files whose parent is subsumed by a subdir glob.
        let file_parent = file.parent().unwrap_or(Path::new("."));
        let parent_subsumed = excludes.iter().any(|exc| {
            exc.strip_suffix("/**/*.nix").is_some_and(|exc_dir| {
                let exc_prefix = format!("{exc_dir}/");
                file_parent
                    .to_str()
                    .is_some_and(|s| s.starts_with(&exc_prefix))
            })
        });
        if !parent_subsumed {
            excludes.push(file.display().to_string());
        }
    }

    excludes
}

/// Generate the tix.toml content from classified files.
fn generate_toml(
    by_kind: &HashMap<NixFileKind, Vec<(PathBuf, Classification)>>,
    _project_root: &Path,
) -> String {
    // Flatten all files for cross-kind conflict detection in derive_glob_patterns.
    let all_files: Vec<(PathBuf, Classification)> = by_kind
        .values()
        .flat_map(|files| files.iter().cloned())
        .collect();

    let mut sections = Vec::new();

    // Header comment.
    sections.push("# tix.toml — generated by `tix init`\n".to_string());

    // Track patterns used by context sections so we can omit them from comments.
    let mut used_patterns: std::collections::HashSet<String> = std::collections::HashSet::new();

    // Context sections (nixos, home-manager, callpackage).
    let context_kinds = [
        (NixFileKind::NixosModule, "nixos", "@nixos"),
        (
            NixFileKind::HomeManagerModule,
            "home-manager",
            "@home-manager",
        ),
        (NixFileKind::CallPackage, "callpackage", "@callpackage"),
    ];
    for (kind, name, stub) in &context_kinds {
        if let Some(files) = by_kind.get(kind) {
            let result = derive_glob_patterns(files, &all_files);
            if !result.paths.is_empty() {
                used_patterns.extend(result.paths.iter().cloned());
                let mut section = format!(
                    "[context.{name}]\npaths = [{}]\n",
                    format_string_array(&result.paths),
                );
                if !result.excludes.is_empty() {
                    section.push_str(&format!(
                        "exclude = [{}]\n",
                        format_string_array(&result.excludes),
                    ));
                }
                section.push_str(&format!("stubs = [\"{stub}\"]\n"));
                sections.push(section);
            }
        }
    }

    // Overlay / Library / Flake files — commented out as informational.
    // Exclude patterns already claimed by a context section.
    for (kind, label) in [
        (NixFileKind::Overlay, "overlay"),
        (NixFileKind::Library, "library"),
        (NixFileKind::Flake, "flake"),
    ] {
        if let Some(files) = by_kind.get(&kind) {
            let result = derive_glob_patterns(files, &all_files);
            let unique: Vec<_> = result
                .paths
                .into_iter()
                .filter(|p| !used_patterns.contains(p))
                .collect();
            if !unique.is_empty() {
                sections.push(format!(
                    "# {label} files (no context needed): {}\n",
                    unique.join(", ")
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
        let result = derive_glob_patterns(&files, &files);
        assert_eq!(result.paths, vec!["modules/**/*.nix"]);
        assert!(result.excludes.is_empty());
    }

    #[test]
    fn derive_globs_single_file_listed() {
        let files = vec![(PathBuf::from("pkgs/foo.nix"), dummy_classification())];
        let result = derive_glob_patterns(&files, &files);
        assert_eq!(result.paths, vec!["pkgs/foo.nix"]);
        assert!(result.excludes.is_empty());
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

    #[test]
    fn derive_globs_removes_paths_subsumed_by_recursive_glob() {
        // Simulates a layout like:
        //   common/homemanager/a.nix        (triggers common/homemanager/**/*.nix)
        //   common/homemanager/b.nix
        //   common/homemanager/claude/default.nix   (subsumed by the glob above)
        //   common/homemanager/fish/default.nix     (subsumed)
        //   common/homemanager/git/default.nix      (subsumed)
        let files = vec![
            (
                PathBuf::from("common/homemanager/a.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/b.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/claude/default.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/fish/default.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/git/default.nix"),
                dummy_classification(),
            ),
        ];
        let result = derive_glob_patterns(&files, &files);
        assert_eq!(result.paths, vec!["common/homemanager/**/*.nix"]);
        assert!(result.excludes.is_empty());
    }

    #[test]
    fn derive_globs_removes_child_globs_subsumed_by_parent() {
        // If common/**/*.nix exists, common/homemanager/**/*.nix is redundant.
        let files = vec![
            (PathBuf::from("common/a.nix"), dummy_classification()),
            (PathBuf::from("common/b.nix"), dummy_classification()),
            (
                PathBuf::from("common/homemanager/a.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/b.nix"),
                dummy_classification(),
            ),
        ];
        let result = derive_glob_patterns(&files, &files);
        assert_eq!(result.paths, vec!["common/**/*.nix"]);
        assert!(result.excludes.is_empty());
    }

    #[test]
    fn derive_globs_mixed_dir_lists_individual_files() {
        // common/ has files of two different kinds — don't emit common/**/*.nix
        // for either kind since it would match the other kind's files too.
        let nixos_files = vec![
            (PathBuf::from("common/a.nix"), dummy_classification()),
            (PathBuf::from("common/b.nix"), dummy_classification()),
        ];
        let library_files = vec![(
            PathBuf::from("common/c.nix"),
            classification(NixFileKind::Library),
        )];
        let all_files: Vec<_> = nixos_files
            .iter()
            .chain(library_files.iter())
            .cloned()
            .collect();

        let result = derive_glob_patterns(&nixos_files, &all_files);
        assert_eq!(
            result.paths,
            vec!["common/a.nix", "common/b.nix"],
            "mixed dir should list individual files, not a recursive glob"
        );
        assert!(result.excludes.is_empty());
    }

    #[test]
    fn derive_globs_mixed_dir_child_still_globs_if_pure() {
        // common/ is mixed, but common/homemanager/ is all one kind.
        let nixos_files = vec![
            (PathBuf::from("common/a.nix"), dummy_classification()),
            (
                PathBuf::from("common/homemanager/a.nix"),
                dummy_classification(),
            ),
            (
                PathBuf::from("common/homemanager/b.nix"),
                dummy_classification(),
            ),
        ];
        let library_files = vec![(
            PathBuf::from("common/c.nix"),
            classification(NixFileKind::Library),
        )];
        let all_files: Vec<_> = nixos_files
            .iter()
            .chain(library_files.iter())
            .cloned()
            .collect();

        let result = derive_glob_patterns(&nixos_files, &all_files);
        assert_eq!(
            result.paths,
            vec!["common/a.nix", "common/homemanager/**/*.nix"],
        );
        assert!(result.excludes.is_empty());
    }

    #[test]
    fn generate_toml_no_duplicate_globs_in_comments() {
        // If pkgs/**/*.nix appears in callpackage context, it shouldn't also
        // appear in the library comment.
        let mut by_kind: HashMap<NixFileKind, Vec<(PathBuf, Classification)>> = HashMap::new();
        by_kind.insert(
            NixFileKind::CallPackage,
            vec![
                (
                    PathBuf::from("pkgs/a.nix"),
                    classification(NixFileKind::CallPackage),
                ),
                (
                    PathBuf::from("pkgs/b.nix"),
                    classification(NixFileKind::CallPackage),
                ),
            ],
        );
        by_kind.insert(
            NixFileKind::Library,
            vec![(
                PathBuf::from("pkgs/c.nix"),
                classification(NixFileKind::Library),
            )],
        );

        let toml = generate_toml(&by_kind, Path::new("/tmp"));
        // The library comment should list pkgs/c.nix individually, not pkgs/**/*.nix.
        assert!(
            !toml.contains("# library files (no context needed): pkgs/**/*.nix"),
            "library comment should not duplicate callpackage glob.\nGot:\n{toml}"
        );
    }

    // When a directory has many this-kind files and few other-kind files,
    // using a dir glob + exclude patterns is more concise than listing
    // every this-kind file individually.
    #[test]
    fn derive_globs_mixed_dir_uses_exclude_when_concise() {
        // 10 nixos files + 2 library files in the same dir → dir/**/*.nix + 2 excludes
        let mut nixos_files: Vec<(PathBuf, Classification)> = (0..10)
            .map(|i| {
                (
                    PathBuf::from(format!("common/nixos{i}.nix")),
                    dummy_classification(),
                )
            })
            .collect();
        // Also add files in a subdirectory to trigger recursive glob.
        nixos_files.push((
            PathBuf::from("common/sub/extra.nix"),
            dummy_classification(),
        ));

        let library_files = vec![
            (
                PathBuf::from("common/lib1.nix"),
                classification(NixFileKind::Library),
            ),
            (
                PathBuf::from("common/lib2.nix"),
                classification(NixFileKind::Library),
            ),
        ];

        let all_files: Vec<_> = nixos_files
            .iter()
            .chain(library_files.iter())
            .cloned()
            .collect();

        let result = derive_glob_patterns(&nixos_files, &all_files);
        // Should use a glob + excludes instead of listing 11 individual files.
        assert!(
            result.paths.iter().any(|p| p.contains("**/*.nix")),
            "should use recursive glob, got: {:?}",
            result.paths
        );
        assert!(
            !result.excludes.is_empty(),
            "should have exclude patterns for the library files"
        );
    }

    // When there are few this-kind files relative to excludes, individual
    // listing is more concise.
    #[test]
    fn derive_globs_mixed_dir_lists_individually_when_not_concise() {
        let nixos_files = vec![
            (PathBuf::from("common/a.nix"), dummy_classification()),
            (PathBuf::from("common/b.nix"), dummy_classification()),
        ];
        let library_files = vec![
            (
                PathBuf::from("common/c.nix"),
                classification(NixFileKind::Library),
            ),
            (
                PathBuf::from("common/d.nix"),
                classification(NixFileKind::Library),
            ),
        ];
        let all_files: Vec<_> = nixos_files
            .iter()
            .chain(library_files.iter())
            .cloned()
            .collect();

        let result = derive_glob_patterns(&nixos_files, &all_files);
        // 2 this-kind, 2 other-kind → individual listing (1 + 2 excludes = 3 > 2 files)
        assert!(
            result.excludes.is_empty(),
            "should not have excludes when individual listing is more concise, got: {:?}",
            result.excludes
        );
        assert_eq!(
            result.paths,
            vec!["common/a.nix", "common/b.nix"],
            "should list files individually"
        );
    }

    // When all other-kind files are in a subdirectory, compress them into a
    // single subdir/**/*.nix exclude pattern.
    #[test]
    fn derive_globs_compresses_subdir_excludes() {
        let mut nixos_files: Vec<(PathBuf, Classification)> = (0..5)
            .map(|i| {
                (
                    PathBuf::from(format!("common/nixos{i}.nix")),
                    dummy_classification(),
                )
            })
            .collect();
        nixos_files.push((
            PathBuf::from("common/sub/extra.nix"),
            dummy_classification(),
        ));

        // 3 library files all in common/hm/ subdirectory.
        let library_files: Vec<(PathBuf, Classification)> = (0..3)
            .map(|i| {
                (
                    PathBuf::from(format!("common/hm/lib{i}.nix")),
                    classification(NixFileKind::Library),
                )
            })
            .collect();

        let all_files: Vec<_> = nixos_files
            .iter()
            .chain(library_files.iter())
            .cloned()
            .collect();

        let result = derive_glob_patterns(&nixos_files, &all_files);
        assert!(
            result.excludes.iter().any(|e| e == "common/hm/**/*.nix"),
            "should compress subdir into glob exclude, got excludes: {:?}",
            result.excludes
        );
    }

    fn dummy_classification() -> Classification {
        Classification {
            kind: NixFileKind::NixosModule,
            confidence: 0.8,
            explicit_context: None,
            reason: "test".into(),
        }
    }

    fn classification(kind: NixFileKind) -> Classification {
        Classification {
            kind,
            confidence: 0.8,
            explicit_context: None,
            reason: "test".into(),
        }
    }
}
