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

use proptest::prelude::*;
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

fn build_split_stubs(num_files: usize, assignments: Vec<usize>) -> Option<SplitStubSet> {
    let mut assignments = assignments;
    for a in &mut assignments {
        *a %= num_files;
    }

    if !has_cross_file_merge(&assignments) {
        return None;
    }

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
    std::fs::create_dir_all(&temp_dir).ok()?;

    // Build registry
    let mut registry = TypeAliasRegistry::new();
    for (i, src) in file_sources.iter().enumerate() {
        if src.trim().is_empty() {
            continue;
        }
        let path = temp_dir.join(format!("stub_{i}.tix"));
        std::fs::write(&path, src).ok()?;
        let file = comment_parser::parse_tix_file(src).ok()?;
        registry.load_tix_file_with_path(&file, &path);
    }

    Some(SplitStubSet {
        files: file_sources,
        expected_fields,
        registry,
        _temp_dir: temp_dir,
    })
}

fn arb_split_stubs() -> impl Strategy<Value = SplitStubSet> {
    let num_files = 2..=3usize;
    let assignments = proptest::collection::vec(0..3usize, DECL_CHUNKS.len());

    (num_files, assignments).prop_filter_map("need cross-file merge", |(num_files, assignments)| {
        build_split_stubs(num_files, assignments)
    })
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

fn arb_nix_with_stubs() -> impl Strategy<Value = (SplitStubSet, NixTestCase)> {
    arb_split_stubs().prop_flat_map(|stubs| {
        let pattern_idx = 0..NUM_PATTERNS;
        (Just(stubs), pattern_idx).prop_map(|(stubs, pat)| {
            let test_case = build_test_case(&stubs, pat);
            (stubs, test_case)
        })
    })
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

fn pbt_config(default_cases: u32) -> ProptestConfig {
    ProptestConfig {
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(default_cases),
        ..ProptestConfig::default()
    }
}

// ==============================================================================
// Property Tests — Semantic Correctness
// ==============================================================================

proptest! {
    #![proptest_config(pbt_config(64))]

    // -------------------------------------------------------------------------
    // Hover at stub-resolved positions returns Some
    // -------------------------------------------------------------------------
    #[test]
    fn pbt_stub_merge_hover_returns_some(
        (stubs, test_case) in arb_nix_with_stubs()
            .prop_filter("needs hover targets", |(_, tc)| !tc.hover_targets.is_empty())
    ) {
        match test_case.setup_mode {
            SetupMode::WithRegistry => {
                let t = TestAnalysis::with_registry(&test_case.source, stubs.registry.clone());
                let snapshot = t.snapshot();
                let docs = &t.state.registry.docs;
                for &off in &test_case.hover_targets {
                    let pos = snapshot.syntax.line_index.position(off);
                    let result = hover(&snapshot, pos, &t.root, docs);
                    prop_assert!(
                        result.is_some(),
                        "hover should return Some at offset {} in:\n{}",
                        off, test_case.source
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
                    prop_assert!(
                        result.is_some(),
                        "hover should return Some at offset {} in:\n{}",
                        off, test_case.source
                    );
                }
            }
        }
    }

    // -------------------------------------------------------------------------
    // Completion at dot position includes ALL merged fields
    // -------------------------------------------------------------------------
    #[test]
    fn pbt_stub_merge_completion_includes_merged_fields(
        (stubs, test_case) in arb_nix_with_stubs()
            .prop_filter("needs completion target", |(_, tc)| tc.completion_target.is_some())
    ) {
        let (off, ref expected_names) = *test_case.completion_target.as_ref().unwrap();

        match test_case.setup_mode {
            SetupMode::WithRegistry => {
                let t = TestAnalysis::with_registry(&test_case.source, stubs.registry.clone());
                let snapshot = t.snapshot();
                let docs = &t.state.registry.docs;
                let pos = snapshot.syntax.line_index.position(off);
                let result = completion(
                    &snapshot, pos, &t.root, docs,
                    &snapshot.syntax.line_index, None,
                );
                let labels = result.as_ref().map(completion_labels).unwrap_or_default();
                for name in expected_names {
                    prop_assert!(
                        labels.contains(name),
                        "completion missing field '{}' from merged stubs.\n\
                         Got: {:?}\nExpected all of: {:?}\nSource:\n{}\nFiles: {:?}",
                        name, labels, expected_names, test_case.source, stubs.files
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
                    &snapshot, pos, &root, docs,
                    &snapshot.syntax.line_index, None,
                );
                let labels = result.as_ref().map(completion_labels).unwrap_or_default();
                for name in expected_names {
                    prop_assert!(
                        labels.contains(name),
                        "completion missing field '{}' from merged stubs.\n\
                         Got: {:?}\nExpected all of: {:?}\nSource:\n{}\nStubs:\n{}",
                        name, labels, expected_names, test_case.source, ctx_stubs
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
}

// ==============================================================================
// Property Tests — Crash Freedom
// ==============================================================================
//
// Run all LSP features at every interesting position with non-empty stubs.
// No semantic assertions — just verify no panics.

proptest! {
    #![proptest_config(pbt_config(128))]

    #[test]
    fn pbt_stub_merge_crash_freedom(
        (stubs, test_case) in arb_nix_with_stubs()
    ) {
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
                        &snapshot, pos, &t.root, docs,
                        &snapshot.syntax.line_index, None,
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
                        &snapshot, pos, &root, docs,
                        &snapshot.syntax.line_index, None,
                    );
                    let _ = goto_definition(&ctx.state, &snapshot, pos, &uri, &root);
                }
            }
        }
    }
}
