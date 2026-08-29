// ==============================================================================
// Property-based tests for LSP features with multi-file stub merging
// ==============================================================================
//
// Generates stub declarations split across 2-3 .tix files, merges them via
// TypeAliasRegistry, and verifies that hover/completion/goto-def work correctly
// on the merged result. Tests three annotation styles:
//   - `/** type: lib :: Lib */` block comment on let bindings
//   - `# type: lib :: Lib` line comment on let bindings and lambda pattern fields
//   - Context args on lambda params (via ContextTestSetup)
//
// Key property: after merging modules from multiple files, ALL fields from ALL
// files appear in LSP results — not just the last-loaded file.

use hegel::generators;
use hegel::TestCase;
use tower_lsp::lsp_types::CompletionResponse;

use crate::completion::completion;
use crate::goto_def::goto_definition;
use crate::hover::hover;
use crate::test_util::{interesting_positions, temp_path, ContextTestSetup, TestAnalysis};
use lang_check::aliases::TypeAliasRegistry;

// ==============================================================================
// Declaration Chunk Pool
// ==============================================================================
//
// Each chunk is a self-contained .tix fragment that contributes fields to a
// module path. Chunks targeting the same module path (e.g., two chunks both
// wrapping `module lib { module strings { ... } }`) exercise recursive merge
// when assigned to different files.

struct DeclChunk {
    /// Tix source text for this chunk
    tix_source: &'static str,
    /// Module path this chunk contributes fields to (e.g. "lib.strings")
    module_path: &'static str,
    /// Field names this chunk adds at the leaf level
    field_names: &'static [&'static str],
}

const DECL_CHUNKS: &[DeclChunk] = &[
    // -- lib.strings chunk A --
    DeclChunk {
        tix_source: "module lib {\n  module strings {\n    val toLower :: string -> string;\n    val toUpper :: string -> string;\n  }\n}\n",
        module_path: "lib.strings",
        field_names: &["toLower", "toUpper"],
    },
    // -- lib.strings chunk B --
    DeclChunk {
        tix_source: "module lib {\n  module strings {\n    val trim :: string -> string;\n    val stringLength :: string -> int;\n  }\n}\n",
        module_path: "lib.strings",
        field_names: &["trim", "stringLength"],
    },
    // -- lib.strings chunk C (extras for 3-file splits) --
    DeclChunk {
        tix_source: "module lib {\n  module strings {\n    val concatStrings :: [string] -> string;\n    val hasPrefix :: string -> string -> bool;\n  }\n}\n",
        module_path: "lib.strings",
        field_names: &["concatStrings", "hasPrefix"],
    },
    // -- lib.lists chunk A --
    DeclChunk {
        tix_source: "module lib {\n  module lists {\n    val head :: [a] -> a;\n    val tail :: [a] -> [a];\n  }\n}\n",
        module_path: "lib.lists",
        field_names: &["head", "tail"],
    },
    // -- lib.lists chunk B --
    DeclChunk {
        tix_source: "module lib {\n  module lists {\n    val length :: [a] -> int;\n    val reverseList :: [a] -> [a];\n  }\n}\n",
        module_path: "lib.lists",
        field_names: &["length", "reverseList"],
    },
    // -- lib top-level vals --
    DeclChunk {
        tix_source: "module lib {\n  val id :: a -> a;\n  val boolToString :: bool -> string;\n}\n",
        module_path: "lib",
        field_names: &["id", "boolToString"],
    },
    // -- lib top-level extras --
    DeclChunk {
        tix_source: "module lib {\n  val map :: (a -> b) -> [a] -> [b];\n  val filter :: (a -> bool) -> [a] -> [a];\n}\n",
        module_path: "lib",
        field_names: &["map", "filter"],
    },
    // -- helper module (separate, no overlap) --
    DeclChunk {
        tix_source: "module helper {\n  val greet :: string -> string;\n  val negate :: bool -> bool;\n}\n",
        module_path: "helper",
        field_names: &["greet", "negate"],
    },
];

// ==============================================================================
// Split Stub Set
// ==============================================================================

#[derive(Clone)]
struct SplitStubSet {
    /// The concatenated tix source for each file
    files: Vec<String>,
    /// All expected fields after merging, keyed by module path
    expected_fields: std::collections::HashMap<String, Vec<String>>,
    /// The merged registry
    registry: TypeAliasRegistry,
    /// Temp directory holding stub files (for goto-def DeclLocation)
    /// NOTE: Not cleaned up on clone — that's fine for test-only code.
    _temp_dir: std::path::PathBuf,
}

impl std::fmt::Debug for SplitStubSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplitStubSet")
            .field("num_files", &self.files.len())
            .field("expected_fields", &self.expected_fields)
            .finish()
    }
}

impl Drop for SplitStubSet {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self._temp_dir);
    }
}

/// Check whether any module path has chunks assigned to different files.
fn has_cross_file_merge(assignments: &[usize]) -> bool {
    let mut path_to_files: std::collections::HashMap<&str, std::collections::HashSet<usize>> =
        std::collections::HashMap::new();
    for (i, chunk) in DECL_CHUNKS.iter().enumerate() {
        path_to_files
            .entry(chunk.module_path)
            .or_default()
            .insert(assignments[i]);
    }
    path_to_files.values().any(|files| files.len() > 1)
}

/// Rewrite `assignments` (chunk index → file index) so at least one module
/// path is split across two files. Draws which chunk pair to split.
fn ensure_cross_file_merge(tc: &TestCase, assignments: &mut [usize], num_files: usize) {
    if has_cross_file_merge(assignments) {
        return;
    }
    let mut by_path: std::collections::HashMap<&str, Vec<usize>> = std::collections::HashMap::new();
    for (i, chunk) in DECL_CHUNKS.iter().enumerate() {
        by_path.entry(chunk.module_path).or_default().push(i);
    }
    let mut mergeable: Vec<Vec<usize>> = by_path.into_values().filter(|v| v.len() > 1).collect();
    mergeable.sort();
    let group = &mergeable[tc.draw(generators::integers::<usize>().max_value(mergeable.len() - 1))];
    let first = group[0];
    let second = group[1];
    let other_file = (assignments[first] + 1) % num_files;
    assignments[second] = other_file;
}

fn build_split_stubs(num_files: usize, assignments: &[usize]) -> SplitStubSet {
    debug_assert!(has_cross_file_merge(assignments));

    // Build file source strings
    let mut file_sources: Vec<String> = vec![String::new(); num_files];
    let mut expected_fields: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();

    for (i, chunk) in DECL_CHUNKS.iter().enumerate() {
        file_sources[assignments[i]].push_str(chunk.tix_source);
        file_sources[assignments[i]].push('\n');
        expected_fields
            .entry(chunk.module_path.to_string())
            .or_default()
            .extend(chunk.field_names.iter().map(|s| s.to_string()));
    }

    // Create temp dir for stub files
    let temp_dir = temp_path("pbt_stubs");
    std::fs::create_dir_all(&temp_dir).expect("create stub temp dir");

    // Build registry
    let mut registry = TypeAliasRegistry::new();
    for (i, src) in file_sources.iter().enumerate() {
        if src.trim().is_empty() {
            continue;
        }
        let path = temp_dir.join(format!("stub_{i}.tix"));
        std::fs::write(&path, src).expect("write stub file");
        let file = comment_parser::parse_tix_file(src).expect("stub chunks parse");
        registry.load_tix_file_with_path(&file, &path);
    }

    SplitStubSet {
        files: file_sources,
        expected_fields,
        registry,
        _temp_dir: temp_dir,
    }
}

/// Stub declarations split across 2-3 files, always with at least one
/// module path merged across files.
fn split_stubs(tc: &TestCase) -> SplitStubSet {
    const MIN_FILES: usize = 2;
    const MAX_FILES: usize = 3;
    let num_files = tc.draw(
        generators::integers::<usize>()
            .min_value(MIN_FILES)
            .max_value(MAX_FILES),
    );
    let mut assignments: Vec<usize> = tc.draw(
        generators::vecs(generators::integers::<usize>().max_value(num_files - 1))
            .min_size(DECL_CHUNKS.len())
            .max_size(DECL_CHUNKS.len()),
    );
    ensure_cross_file_merge(tc, &mut assignments, num_files);
    build_split_stubs(num_files, &assignments)
}

// ==============================================================================
// Nix Source Patterns
// ==============================================================================

#[derive(Debug, Clone)]
enum SetupMode {
    /// Use TestAnalysis::with_registry — in-memory, fast
    WithRegistry,
    /// Use ContextTestSetup — writes stubs to disk, supports context args
    ContextSetup,
}

#[derive(Debug, Clone)]
struct NixTestCase {
    source: String,
    /// Byte offsets where hover should return Some
    hover_targets: Vec<u32>,
    /// Completion target: (byte_offset, expected_field_names)
    completion_target: Option<(u32, Vec<String>)>,
    setup_mode: SetupMode,
    /// Combined context stubs text (only for ContextSetup mode)
    context_stubs: Option<String>,
}

/// Pick a field name from a module path in the expected fields map.
/// Falls back to "id" if the path doesn't exist.
fn pick_field<'a>(
    expected: &'a std::collections::HashMap<String, Vec<String>>,
    module_path: &str,
) -> &'a str {
    expected
        .get(module_path)
        .and_then(|fields| fields.first())
        .map(|s| s.as_str())
        .unwrap_or("id")
}

/// Get all expected field names for a module path.
fn expected_at(
    expected: &std::collections::HashMap<String, Vec<String>>,
    module_path: &str,
) -> Vec<String> {
    expected.get(module_path).cloned().unwrap_or_default()
}

/// Build the combined context stubs for ContextSetup mode.
/// Concatenates all stub files and adds `val lib :: Lib;` for context arg typing.
fn combined_context_stubs(files: &[String]) -> String {
    let mut out = String::new();
    for f in files {
        out.push_str(f);
        out.push('\n');
    }
    out.push_str("val lib :: Lib;\n");
    out
}

fn find_offset(src: &str, pattern: &str) -> u32 {
    src.find(pattern).expect("pattern not found in source") as u32
}

/// Build a NixTestCase for a given pattern index and stub set.
fn build_test_case(stubs: &SplitStubSet, pattern: usize) -> NixTestCase {
    match pattern {
        // Pattern 1: Block comment annotation on lambda pattern field, field access
        0 => {
            let field = pick_field(&stubs.expected_fields, "lib.strings");
            let src = format!(
                "{{\n    /** type: lib :: Lib */\n    lib,\n    ...\n}}: lib.strings.{field} \"hi\""
            );
            let hover_off = find_offset(&src, &format!(".{field}"));
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        // Pattern 2: Line comment annotation on lambda pattern field, field access
        1 => {
            let field = pick_field(&stubs.expected_fields, "lib.strings");
            let src = format!(
                "{{\n    # type: lib :: Lib\n    lib,\n    ...\n}}: lib.strings.{field} \"hi\""
            );
            let hover_off = find_offset(&src, &format!(".{field}"));
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        // Pattern 3: Block comment annotation on let binding, field access
        // The value is an attrset with matching fields to satisfy bidirectional
        // constraint. The annotation adds the Lib alias name.
        2 => {
            let field = pick_field(&stubs.expected_fields, "lib.strings");
            let src = format!(
                "let\n    /** type: lib :: Lib */\n    lib = {{ strings = {{ {field} = x: x; }}; }};\nin lib.strings.{field} \"hi\""
            );
            let hover_off = find_offset(&src, &format!("in lib.strings.{field}"))
                + "in lib.strings".len() as u32;
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        // Pattern 4: Line comment annotation on let binding, field access
        3 => {
            let field = pick_field(&stubs.expected_fields, "lib.strings");
            let src = format!(
                "let\n    # type: lib :: Lib\n    lib = {{ strings = {{ {field} = x: x; }}; }};\nin lib.strings.{field} \"hi\""
            );
            let hover_off = find_offset(&src, &format!("in lib.strings.{field}"))
                + "in lib.strings".len() as u32;
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        // Pattern 5: Context args on lambda pattern field
        4 => {
            let field = pick_field(&stubs.expected_fields, "lib.strings");
            let src = format!("{{ lib, ... }}: lib.strings.{field} \"hi\"");
            let hover_off = find_offset(&src, &format!(".{field}"));
            let ctx = combined_context_stubs(&stubs.files);
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::ContextSetup,
                context_stubs: Some(ctx),
            }
        }

        // Pattern 6: Lambda pattern annotation, completion at lib.strings.
        // Trailing dot (incomplete Select) triggers dot completion.
        5 => {
            let src = "{\n    # type: lib :: Lib\n    lib,\n    ...\n}: lib.strings.\n".to_string();
            let cursor_off = find_offset(&src, "strings.") + "strings.".len() as u32;
            let expected = expected_at(&stubs.expected_fields, "lib.strings");
            NixTestCase {
                source: src,
                hover_targets: vec![],
                completion_target: Some((cursor_off, expected)),
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        // Pattern 7: Context args, completion at lib.
        6 => {
            let src = "{ lib, ... }: lib.\n".to_string();
            let cursor_off = find_offset(&src, "}: lib.") + "}: lib.".len() as u32;
            // At lib. we expect all top-level lib fields plus sub-modules
            let mut expected = expected_at(&stubs.expected_fields, "lib");
            if stubs.expected_fields.contains_key("lib.strings") {
                expected.push("strings".to_string());
            }
            if stubs.expected_fields.contains_key("lib.lists") {
                expected.push("lists".to_string());
            }
            let ctx = combined_context_stubs(&stubs.files);
            NixTestCase {
                source: src,
                hover_targets: vec![],
                completion_target: Some((cursor_off, expected)),
                setup_mode: SetupMode::ContextSetup,
                context_stubs: Some(ctx),
            }
        }

        // Pattern 8: Block comment on let, helper module (non-overlapping)
        7 => {
            let field = pick_field(&stubs.expected_fields, "helper");
            let src = format!(
                "{{\n    /** type: h :: Helper */\n    h,\n    ...\n}}: h.{field} \"world\""
            );
            let hover_off = find_offset(&src, &format!(".{field}"));
            NixTestCase {
                source: src,
                hover_targets: vec![hover_off],
                completion_target: None,
                setup_mode: SetupMode::WithRegistry,
                context_stubs: None,
            }
        }

        _ => unreachable!(),
    }
}

const NUM_PATTERNS: usize = 8;

/// Split stubs plus one usage pattern; `accept` restricts which patterns
/// may be drawn (e.g. only those with hover targets).
fn nix_with_stubs(tc: &TestCase, accept: fn(&NixTestCase) -> bool) -> (SplitStubSet, NixTestCase) {
    let stubs = split_stubs(tc);
    let candidates: Vec<NixTestCase> = (0..NUM_PATTERNS)
        .map(|pat| build_test_case(&stubs, pat))
        .filter(|case| accept(case))
        .collect();
    assert!(!candidates.is_empty(), "no pattern satisfies the filter");
    let idx = tc.draw(generators::integers::<usize>().max_value(candidates.len() - 1));
    let test_case = candidates.into_iter().nth(idx).expect("idx in range");
    (stubs, test_case)
}

fn any_pattern(_: &NixTestCase) -> bool {
    true
}

// ==============================================================================
// Test Execution
// ==============================================================================

/// Extract CompletionItem labels from a CompletionResponse.
fn completion_labels(resp: &CompletionResponse) -> Vec<String> {
    match resp {
        CompletionResponse::Array(items) => items.iter().map(|i| i.label.clone()).collect(),
        CompletionResponse::List(list) => list.items.iter().map(|i| i.label.clone()).collect(),
    }
}

// ==============================================================================
// Property Tests — Semantic Correctness
// ==============================================================================

const SEMANTIC_CASES: u64 = 64;
const CRASH_CASES: u64 = 128;

/// Hover at stub-resolved positions returns Some.
#[hegel::test(test_cases = SEMANTIC_CASES)]
fn pbt_stub_merge_hover_returns_some(tc: TestCase) {
    let (stubs, test_case) = nix_with_stubs(&tc, |case| !case.hover_targets.is_empty());
    match test_case.setup_mode {
        SetupMode::WithRegistry => {
            let t = TestAnalysis::with_registry(&test_case.source, stubs.registry.clone());
            let snapshot = t.snapshot();
            let docs = &t.state.registry.docs;
            for &off in &test_case.hover_targets {
                let pos = snapshot.syntax.line_index.position(off);
                let result = hover(&snapshot, pos, &t.root, docs);
                assert!(
                    result.is_some(),
                    "hover should return Some at offset {off} in:\n{}",
                    test_case.source
                );
            }
        }
        SetupMode::ContextSetup => {
            let ctx_stubs = test_case.context_stubs.as_deref().unwrap();
            let ctx = ContextTestSetup::new(&test_case.source, ctx_stubs);
            let snapshot = ctx.snapshot();
            let docs = ctx.docs();
            let root = ctx.root();
            for &off in &test_case.hover_targets {
                let pos = snapshot.syntax.line_index.position(off);
                let result = hover(&snapshot, pos, &root, docs);
                assert!(
                    result.is_some(),
                    "hover should return Some at offset {off} in:\n{}",
                    test_case.source
                );
            }
        }
    }
}

/// Completion at the dot position includes ALL merged fields.
#[hegel::test(test_cases = SEMANTIC_CASES)]
fn pbt_stub_merge_completion_includes_merged_fields(tc: TestCase) {
    let (stubs, test_case) = nix_with_stubs(&tc, |case| case.completion_target.is_some());
    let (off, ref expected_names) = *test_case.completion_target.as_ref().unwrap();

    match test_case.setup_mode {
        SetupMode::WithRegistry => {
            let t = TestAnalysis::with_registry(&test_case.source, stubs.registry.clone());
            let snapshot = t.snapshot();
            let docs = &t.state.registry.docs;
            let pos = snapshot.syntax.line_index.position(off);
            let result = completion(
                &snapshot,
                pos,
                &t.root,
                docs,
                &snapshot.syntax.line_index,
                None,
            );
            let labels = result.as_ref().map(completion_labels).unwrap_or_default();
            for name in expected_names {
                assert!(
                    labels.contains(name),
                    "completion missing field '{name}' from merged stubs.\n\
                     Got: {labels:?}\nExpected all of: {expected_names:?}\nSource:\n{}\nFiles: {:?}",
                    test_case.source, stubs.files
                );
            }
        }
        SetupMode::ContextSetup => {
            let ctx_stubs = test_case.context_stubs.as_deref().unwrap();
            let ctx = ContextTestSetup::new(&test_case.source, ctx_stubs);
            let snapshot = ctx.snapshot();
            let docs = ctx.docs();
            let root = ctx.root();
            let pos = snapshot.syntax.line_index.position(off);
            let result = completion(
                &snapshot,
                pos,
                &root,
                docs,
                &snapshot.syntax.line_index,
                None,
            );
            let labels = result.as_ref().map(completion_labels).unwrap_or_default();
            for name in expected_names {
                assert!(
                    labels.contains(name),
                    "completion missing field '{name}' from merged stubs.\n\
                     Got: {labels:?}\nExpected all of: {expected_names:?}\nSource:\n{}\nStubs:\n{ctx_stubs}",
                    test_case.source
                );
            }
        }
    }
}

// Goto-def crash freedom is covered by pbt_stub_merge_crash_freedom.
// Semantic goto-def assertions for stub-declared names are complex because
// the LSP's Select field lookup depends on source_map expr resolution,
// which varies by annotation style. The crash-freedom test ensures goto-def
// doesn't panic at any position with non-empty stubs.

// ==============================================================================
// Property Tests — Crash Freedom
// ==============================================================================
//
// Run all LSP features at every interesting position with non-empty stubs.
// No semantic assertions — just verify no panics.

#[hegel::test(test_cases = CRASH_CASES)]
fn pbt_stub_merge_crash_freedom(tc: TestCase) {
    let (stubs, test_case) = nix_with_stubs(&tc, any_pattern);
    match test_case.setup_mode {
        SetupMode::WithRegistry => {
            let t = TestAnalysis::with_registry(&test_case.source, stubs.registry.clone());
            let analysis = t.analysis();
            let snapshot = t.snapshot();
            let docs = &t.state.registry.docs;
            let uri = t.uri();
            let positions = interesting_positions(analysis, &t.root);
            for ip in &positions {
                let pos = snapshot.syntax.line_index.position(ip.byte_offset());
                let _ = hover(&snapshot, pos, &t.root, docs);
                let _ = completion(
                    &snapshot,
                    pos,
                    &t.root,
                    docs,
                    &snapshot.syntax.line_index,
                    None,
                );
                let _ = goto_definition(&t.state, &snapshot, pos, &uri, &t.root);
            }
        }
        SetupMode::ContextSetup => {
            let ctx_stubs = test_case.context_stubs.as_deref().unwrap();
            let ctx = ContextTestSetup::new(&test_case.source, ctx_stubs);
            let analysis = ctx.analysis();
            let snapshot = ctx.snapshot();
            let docs = ctx.docs();
            let root = ctx.root();
            let uri = tower_lsp::lsp_types::Url::from_file_path(&ctx.nix_path).unwrap();
            let positions = interesting_positions(analysis, &root);
            for ip in &positions {
                let pos = snapshot.syntax.line_index.position(ip.byte_offset());
                let _ = hover(&snapshot, pos, &root, docs);
                let _ = completion(
                    &snapshot,
                    pos,
                    &root,
                    docs,
                    &snapshot.syntax.line_index,
                    None,
                );
                let _ = goto_definition(&ctx.state, &snapshot, pos, &uri, &root);
            }
        }
    }
}
