use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use tower_lsp::lsp_types::Url;

use crate::state::{AnalysisState, FileAnalysis};
use lang_check::aliases::TypeAliasRegistry;

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
        let root = rnix::Root::parse(src).tree();
        Self { state, path, root }
    }

    pub fn analysis(&self) -> &FileAnalysis {
        self.state.get_file(&self.path).unwrap()
    }

    pub fn uri(&self) -> Url {
        Url::from_file_path(&self.path).unwrap()
    }
}
