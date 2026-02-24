use std::collections::{BTreeMap, HashSet};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use lang_ast::Expr;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::Url;

use crate::project_config::{ContextConfig, ProjectConfig};
use crate::state::{AnalysisState, FileAnalysis};
use lang_check::aliases::{DocIndex, TypeAliasRegistry};

static COUNTER: AtomicU32 = AtomicU32::new(0);

/// Generate a unique temporary file path for tests, avoiding collisions
/// when tests run in parallel.
pub fn temp_path(name: &str) -> PathBuf {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("tix_test_{}_{id}_{name}", std::process::id()))
}

/// Find the byte offset of a pattern in source text.
pub fn find_offset(src: &str, pattern: &str) -> u32 {
    src.find(pattern).expect("pattern not found in source") as u32
}

/// Parse `# ^<num>` marker comments from source.
///
/// Embed `# ^<num>` comments in test source where `^` points to the column
/// on the **previous line** where the cursor should be, and `<num>` is a
/// marker ID. Since `#` is a valid Nix comment, markers don't affect parsing.
///
/// Returns a BTreeMap from marker number to byte offset on the previous line.
pub fn parse_markers(src: &str) -> BTreeMap<u32, u32> {
    let mut markers = BTreeMap::new();
    let lines: Vec<&str> = src.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if !trimmed.starts_with('#') {
            continue;
        }

        let mut search_from = 0;
        while let Some(caret_pos) = line[search_from..].find('^') {
            let abs_caret_pos = search_from + caret_pos;
            let after_caret = &line[abs_caret_pos + 1..];

            // Parse the marker number immediately after `^`.
            let num_str: String = after_caret
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            if num_str.is_empty() {
                search_from = abs_caret_pos + 1;
                continue;
            }
            let marker_num: u32 = num_str.parse().unwrap();

            // The column of `^` on the marker line corresponds to the
            // same column on the PREVIOUS line.
            assert!(line_idx > 0, "marker on first line has no previous line");
            let prev_line_start: usize = lines[..line_idx - 1]
                .iter()
                .map(|l| l.len() + 1) // +1 for the newline
                .sum();

            let byte_offset = (prev_line_start + abs_caret_pos) as u32;
            markers.insert(marker_num, byte_offset);
            search_from = abs_caret_pos + 1 + num_str.len();
        }
    }

    markers
}

/// A temporary directory with Nix files for multi-file LSP tests.
///
/// Files are written as `(relative_name, contents)` pairs. The directory
/// and all its contents are cleaned up on drop.
pub struct TempProject {
    dir: PathBuf,
}

impl TempProject {
    pub fn new(files: &[(&str, &str)]) -> Self {
        let dir = temp_path("project");
        std::fs::create_dir_all(&dir).expect("create temp dir");
        for (name, contents) in files {
            let path = dir.join(name);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).expect("create parent dirs");
            }
            std::fs::write(&path, contents).expect("write temp file");
        }
        TempProject { dir }
    }

    pub fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name).canonicalize().expect("canonicalize")
    }
}

impl Drop for TempProject {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Single-file analysis setup for LSP tests.
///
/// Encapsulates the common pattern of creating a temp file, initializing
/// `AnalysisState`, parsing, and providing access to `FileAnalysis`.
pub struct TestAnalysis {
    pub state: AnalysisState,
    pub path: PathBuf,
    pub root: rnix::Root,
}

impl TestAnalysis {
    pub fn new(src: &str) -> Self {
        Self::with_registry(src, TypeAliasRegistry::default())
    }

    pub fn with_registry(src: &str, registry: TypeAliasRegistry) -> Self {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(registry);
        state.update_file(path.clone(), src.to_string());
        let root = state.get_file(&path).unwrap().parsed.tree();
        Self { state, path, root }
    }

    pub fn analysis(&self) -> &FileAnalysis {
        self.state.get_file(&self.path).unwrap()
    }

    pub fn uri(&self) -> Url {
        Url::from_file_path(&self.path).unwrap()
    }
}

/// Test setup with context stubs (`.tix` declarations) injected via ProjectConfig.
///
/// Used by both completion and hover tests that need NixOS module context.
/// Creates a temp directory with the stubs file, configures a ProjectConfig
/// that matches all `.nix` files, runs analysis, and cleans up on drop.
pub struct ContextTestSetup {
    pub state: AnalysisState,
    pub nix_path: PathBuf,
    temp_dir: PathBuf,
}

impl ContextTestSetup {
    pub fn new(src: &str, context_stubs: &str) -> Self {
        let temp_dir = temp_path("ctx");
        std::fs::create_dir_all(&temp_dir).unwrap();

        // Write context stubs to a file in the temp directory.
        let stubs_path = temp_dir.join("test_context.tix");
        std::fs::write(&stubs_path, context_stubs).unwrap();

        let nix_path = temp_dir.join("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());

        // Configure project context: all .nix files get our test context stubs.
        let mut context = std::collections::HashMap::new();
        context.insert(
            "test".to_string(),
            ContextConfig {
                paths: vec!["*.nix".to_string()],
                stubs: vec!["test_context.tix".to_string()],
            },
        );
        state.project_config = Some(ProjectConfig {
            stubs: vec![],
            context,
            deadline: None,
        });
        state.config_dir = Some(temp_dir.clone());

        state.update_file(nix_path.clone(), src.to_string());

        Self {
            state,
            nix_path,
            temp_dir,
        }
    }

    pub fn analysis(&self) -> &FileAnalysis {
        self.state.get_file(&self.nix_path).unwrap()
    }

    pub fn docs(&self) -> &DocIndex {
        &self.state.registry.docs
    }

    pub fn root(&self) -> rnix::Root {
        self.analysis().parsed.tree()
    }
}

impl Drop for ContextTestSetup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.temp_dir);
    }
}

// ==============================================================================
// Position enumeration for PBT
// ==============================================================================

/// Categories of cursor positions that exercise different LSP code paths.
#[derive(Debug, Clone)]
pub enum InterestingPosition {
    /// On a name binding (let x = ..., { x ? default, ... }: ..., etc.)
    NameBinding { byte_offset: u32 },
    /// On a name reference (a variable use site)
    NameReference { byte_offset: u32 },
    /// On an expression node (any mapped expression)
    Expression { byte_offset: u32 },
}

impl InterestingPosition {
    pub fn byte_offset(&self) -> u32 {
        match self {
            Self::NameBinding { byte_offset }
            | Self::NameReference { byte_offset }
            | Self::Expression { byte_offset } => *byte_offset,
        }
    }
}

/// Extract all interesting cursor positions from an analyzed file.
///
/// Walks the module's names and expressions via the source map to collect
/// positions that would exercise different LSP code paths (hover, goto-def,
/// completion, etc.). Deduplicates by byte offset.
pub fn interesting_positions(
    analysis: &FileAnalysis,
    root: &rnix::Root,
) -> Vec<InterestingPosition> {
    let mut seen = HashSet::new();
    let mut positions = Vec::new();

    // Name bindings: let-bound names, lambda params, pattern fields, etc.
    for (name_id, _name) in analysis.module.names() {
        if let Some(ptr) = analysis.source_map.nodes_for_name(name_id).next() {
            let offset = ptr.to_node(root.syntax()).text_range().start();
            let offset = u32::from(offset);
            if seen.insert(offset) {
                positions.push(InterestingPosition::NameBinding {
                    byte_offset: offset,
                });
            }
        }
    }

    // Expressions: references go into NameReference, everything else into Expression.
    for (expr_id, expr) in analysis.module.exprs() {
        if let Some(ptr) = analysis.source_map.node_for_expr(expr_id) {
            let offset = ptr.to_node(root.syntax()).text_range().start();
            let offset = u32::from(offset);
            if !seen.insert(offset) {
                continue;
            }
            if matches!(expr, Expr::Reference(_)) {
                positions.push(InterestingPosition::NameReference {
                    byte_offset: offset,
                });
            } else {
                positions.push(InterestingPosition::Expression {
                    byte_offset: offset,
                });
            }
        }
    }

    positions
}
