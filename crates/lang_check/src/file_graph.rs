// ==============================================================================
// File-Level Dependency Graph & Layered Ordering
// ==============================================================================
//
// Builds a file-level dependency graph from import scanning results, computes
// SCCs via Tarjan's algorithm, and topologically sorts them into layers.
// Files in the same layer have no dependencies on each other (or are in the
// same SCC) and can be inferred in parallel. Dependencies from prior layers
// are guaranteed to already have cached signatures.
//
// This enables cross-file type flow in batch mode (`tix check`) without the
// OOM risk of caching all signatures simultaneously — a reference-counted
// eviction strategy keeps only the "frontier" of needed signatures alive.

use rustc_hash::FxHashMap as HashMap;
use std::path::{Path, PathBuf};

use petgraph::algo::{condensation, toposort};
use petgraph::graph::{DiGraph, NodeIndex};

/// A group of files forming a strongly connected component.
pub struct SccGroup {
    pub files: Vec<PathBuf>,
    /// True if this SCC has >1 file (mutual imports) or a single file that
    /// imports itself. Cyclic SCCs benefit from fixpoint iteration.
    pub is_cyclic: bool,
}

/// A layer of SCCs at the same topological depth. All dependencies from
/// prior layers are guaranteed to have cached signatures before this layer
/// runs.
pub struct InferenceLayer {
    pub sccs: Vec<SccGroup>,
}

impl InferenceLayer {
    /// Flat list of all files in this layer (convenience for eviction logic).
    pub fn all_files(&self) -> impl Iterator<Item = &PathBuf> {
        self.sccs.iter().flat_map(|scc| scc.files.iter())
    }
}

/// Build inference layers preserving SCC grouping.
///
/// Like `build_file_layers`, but each layer contains a list of `SccGroup`s
/// rather than a flat file list. This allows callers to identify which files
/// are in non-trivial (cyclic) SCCs and apply fixpoint iteration to them.
///
/// O(V+E) overall — trivial for even 40K files.
pub fn build_file_layers_with_sccs(
    file_imports: &HashMap<PathBuf, Vec<PathBuf>>,
) -> Vec<InferenceLayer> {
    if file_imports.is_empty() {
        return vec![];
    }

    // =========================================================================
    // Step A: Build the raw file graph and condensation DAG
    // =========================================================================

    let mut graph: DiGraph<PathBuf, ()> = DiGraph::new();
    let mut node_map: HashMap<&Path, NodeIndex> = HashMap::default();

    for path in file_imports.keys() {
        let idx = graph.add_node(path.clone());
        node_map.insert(path.as_path(), idx);
    }

    // Track self-edges before condensation (condensation strips them).
    let mut has_self_edge: rustc_hash::FxHashSet<NodeIndex> = rustc_hash::FxHashSet::default();

    for (importer, deps) in file_imports {
        let from = node_map[importer.as_path()];
        for dep in deps {
            if let Some(&to) = node_map.get(dep.as_path()) {
                if from == to {
                    has_self_edge.insert(from);
                }
                graph.add_edge(from, to, ());
            }
        }
    }

    // Map from original graph NodeIndex → condensed SCC NodeIndex so we can
    // check self-edges on singleton SCCs.
    let mut original_to_condensed: HashMap<NodeIndex, NodeIndex> = HashMap::default();

    let condensed = condensation(graph, true);

    // Build reverse mapping: for each condensed node, record which original
    // nodes are members.
    for cnode in condensed.node_indices() {
        for original_path in &condensed[cnode] {
            if let Some(&orig_idx) = node_map.get(original_path.as_path()) {
                original_to_condensed.insert(orig_idx, cnode);
            }
        }
    }

    // =========================================================================
    // Step B: Compute depth and group into layers (preserving SCC structure)
    // =========================================================================

    let topo_order = match toposort(&condensed, None) {
        Ok(order) => order,
        Err(_) => {
            // Should never happen on a condensation DAG, but handle gracefully.
            let all_files: Vec<PathBuf> = file_imports.keys().cloned().collect();
            return vec![InferenceLayer {
                sccs: vec![SccGroup {
                    files: all_files,
                    is_cyclic: true,
                }],
            }];
        }
    };

    let mut depth: HashMap<NodeIndex, usize> =
        HashMap::with_capacity_and_hasher(topo_order.len(), Default::default());

    for &node in topo_order.iter().rev() {
        let max_dep_depth = condensed
            .neighbors(node)
            .filter_map(|succ| depth.get(&succ))
            .max()
            .copied();

        let node_depth = match max_dep_depth {
            Some(d) => d + 1,
            None => 0,
        };
        depth.insert(node, node_depth);
    }

    let max_depth = depth.values().copied().max().unwrap_or(0);
    let mut layers: Vec<InferenceLayer> = (0..=max_depth)
        .map(|_| InferenceLayer { sccs: Vec::new() })
        .collect();

    for (&cnode, &d) in &depth {
        let files: Vec<PathBuf> = condensed[cnode].to_vec();
        let is_cyclic = if files.len() > 1 {
            true
        } else {
            // Single-file SCC: cyclic only if it imports itself.
            files
                .first()
                .and_then(|p| node_map.get(p.as_path()))
                .is_some_and(|orig_idx| has_self_edge.contains(orig_idx))
        };
        layers[d].sccs.push(SccGroup { files, is_cyclic });
    }

    layers.retain(|l| !l.sccs.is_empty());
    layers
}

/// Build inference layers from a file-level import graph.
///
/// Input: map from canonical file path → list of its canonical import targets
/// (already filtered to in-project files by the caller).
///
/// Returns layers ordered by depth (layer 0 = leaves with no in-project
/// dependencies, processed first). Files within the same SCC are grouped
/// into a single layer. Independent files at the same topological depth
/// share a layer so they can be inferred in parallel.
///
/// O(V+E) overall — trivial for even 40K files.
pub fn build_file_layers(file_imports: &HashMap<PathBuf, Vec<PathBuf>>) -> Vec<Vec<PathBuf>> {
    build_file_layers_with_sccs(file_imports)
        .into_iter()
        .map(|layer| layer.sccs.into_iter().flat_map(|scc| scc.files).collect())
        .collect()
}

/// Compute importer counts for reference-counted eviction.
///
/// Returns a map from each file to the number of in-project files that import
/// it. Files with 0 importers (leaves that nobody depends on) are not present
/// in the map.
pub fn compute_importer_counts(
    file_imports: &HashMap<PathBuf, Vec<PathBuf>>,
) -> HashMap<PathBuf, usize> {
    let mut counts: HashMap<PathBuf, usize> = HashMap::default();
    let project_files: rustc_hash::FxHashSet<&PathBuf> = file_imports.keys().collect();

    for deps in file_imports.values() {
        for dep in deps {
            // Only count in-project dependencies.
            if project_files.contains(dep) {
                *counts.entry(dep.clone()).or_default() += 1;
            }
        }
    }
    counts
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a HashMap from a list of (file, deps) pairs using
    /// simple string paths for readability.
    fn edges(pairs: &[(&str, &[&str])]) -> HashMap<PathBuf, Vec<PathBuf>> {
        pairs
            .iter()
            .map(|(file, deps)| {
                (
                    PathBuf::from(file),
                    deps.iter().map(PathBuf::from).collect(),
                )
            })
            .collect()
    }

    /// Helper: sort a layer's file names for deterministic comparison.
    fn sorted_names(layer: &[PathBuf]) -> Vec<String> {
        let mut names: Vec<String> = layer
            .iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn linear_chain() {
        // A → B → C
        let imports = edges(&[("A", &["B"]), ("B", &["C"]), ("C", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 3);
        assert_eq!(sorted_names(&layers[0]), vec!["C"]);
        assert_eq!(sorted_names(&layers[1]), vec!["B"]);
        assert_eq!(sorted_names(&layers[2]), vec!["A"]);
    }

    #[test]
    fn diamond() {
        // A → {B, C}, B → D, C → D
        let imports = edges(&[("A", &["B", "C"]), ("B", &["D"]), ("C", &["D"]), ("D", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 3);
        assert_eq!(sorted_names(&layers[0]), vec!["D"]);
        assert_eq!(sorted_names(&layers[1]), vec!["B", "C"]);
        assert_eq!(sorted_names(&layers[2]), vec!["A"]);
    }

    #[test]
    fn no_imports_single_layer() {
        // All independent files → single layer
        let imports = edges(&[("A", &[]), ("B", &[]), ("C", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 1);
        assert_eq!(sorted_names(&layers[0]), vec!["A", "B", "C"]);
    }

    #[test]
    fn cycle_single_scc() {
        // A ↔ B (mutual import)
        let imports = edges(&[("A", &["B"]), ("B", &["A"])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 1);
        assert_eq!(sorted_names(&layers[0]), vec!["A", "B"]);
    }

    #[test]
    fn cycle_with_deps() {
        // A ↔ B, both → C
        let imports = edges(&[("A", &["B", "C"]), ("B", &["A", "C"]), ("C", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 2);
        assert_eq!(sorted_names(&layers[0]), vec!["C"]);
        assert_eq!(sorted_names(&layers[1]), vec!["A", "B"]);
    }

    #[test]
    fn import_outside_project_dropped() {
        // A → B, A → /external (not in project set)
        let imports = edges(&[("A", &["B", "/external"]), ("B", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 2);
        assert_eq!(sorted_names(&layers[0]), vec!["B"]);
        assert_eq!(sorted_names(&layers[1]), vec!["A"]);
    }

    #[test]
    fn wide_tree() {
        // A → D, B → D, C → D (3 independent importers)
        let imports = edges(&[("A", &["D"]), ("B", &["D"]), ("C", &["D"]), ("D", &[])]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 2);
        assert_eq!(sorted_names(&layers[0]), vec!["D"]);
        assert_eq!(sorted_names(&layers[1]), vec!["A", "B", "C"]);
    }

    #[test]
    fn empty_input() {
        let imports = HashMap::default();
        let layers = build_file_layers(&imports);
        assert!(layers.is_empty());
    }

    #[test]
    fn complex_dag() {
        // E → D → C → A, E → C, D → B → A
        // Expected depths: A=0, B=1, C=1 (C→A), D=2 (D→B and D→C), E=3
        // Wait, let me reconsider:
        // A has no deps → depth 0
        // B → A → depth 1
        // C → A → depth 1
        // D → {B, C} → depth 2
        // E → {C, D} → depth 3
        let imports = edges(&[
            ("A", &[]),
            ("B", &["A"]),
            ("C", &["A"]),
            ("D", &["B", "C"]),
            ("E", &["C", "D"]),
        ]);

        let layers = build_file_layers(&imports);

        assert_eq!(layers.len(), 4);
        assert_eq!(sorted_names(&layers[0]), vec!["A"]);
        assert_eq!(sorted_names(&layers[1]), vec!["B", "C"]);
        assert_eq!(sorted_names(&layers[2]), vec!["D"]);
        assert_eq!(sorted_names(&layers[3]), vec!["E"]);
    }

    #[test]
    fn importer_counts_basic() {
        // A → D, B → D, C → D
        let imports = edges(&[("A", &["D"]), ("B", &["D"]), ("C", &["D"]), ("D", &[])]);

        let counts = compute_importer_counts(&imports);

        assert_eq!(counts.get(&PathBuf::from("D")), Some(&3));
        // A, B, C have no importers.
        assert_eq!(counts.get(&PathBuf::from("A")), None);
        assert_eq!(counts.get(&PathBuf::from("B")), None);
        assert_eq!(counts.get(&PathBuf::from("C")), None);
    }

    #[test]
    fn importer_counts_excludes_external() {
        // A → B, A → /external (not in project)
        let imports = edges(&[("A", &["B", "/external"]), ("B", &[])]);

        let counts = compute_importer_counts(&imports);

        assert_eq!(counts.get(&PathBuf::from("B")), Some(&1));
        // /external not counted (not in project set).
        assert_eq!(counts.get(&PathBuf::from("/external")), None);
    }

    // =========================================================================
    // build_file_layers_with_sccs tests
    // =========================================================================

    /// Helper: get sorted file names from an SccGroup.
    fn scc_names(scc: &super::SccGroup) -> Vec<String> {
        let mut names: Vec<String> = scc
            .files
            .iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn scc_cycle_is_marked_cyclic() {
        // A ↔ B
        let imports = edges(&[("A", &["B"]), ("B", &["A"])]);
        let layers = build_file_layers_with_sccs(&imports);

        assert_eq!(layers.len(), 1);
        assert_eq!(layers[0].sccs.len(), 1);
        assert!(layers[0].sccs[0].is_cyclic);
        assert_eq!(scc_names(&layers[0].sccs[0]), vec!["A", "B"]);
    }

    #[test]
    fn scc_independent_files_are_separate_groups() {
        // A, B, C independent — same depth, separate non-cyclic SCCs.
        let imports = edges(&[("A", &[]), ("B", &[]), ("C", &[])]);
        let layers = build_file_layers_with_sccs(&imports);

        assert_eq!(layers.len(), 1);
        // Each file is its own SCC.
        assert_eq!(layers[0].sccs.len(), 3);
        for scc in &layers[0].sccs {
            assert!(!scc.is_cyclic);
            assert_eq!(scc.files.len(), 1);
        }
    }

    #[test]
    fn scc_mixed_layer_cycle_plus_singleton() {
        // A ↔ B, both → C. Also D → C (independent of the cycle).
        // Layer 0: C (singleton). Layer 1: {A,B} (cycle) + D (singleton).
        let imports = edges(&[
            ("A", &["B", "C"]),
            ("B", &["A", "C"]),
            ("C", &[]),
            ("D", &["C"]),
        ]);
        let layers = build_file_layers_with_sccs(&imports);

        assert_eq!(layers.len(), 2);
        // Layer 0: just C
        assert_eq!(layers[0].sccs.len(), 1);
        assert!(!layers[0].sccs[0].is_cyclic);

        // Layer 1: one cyclic SCC {A,B} and one singleton D
        assert_eq!(layers[1].sccs.len(), 2);
        let cyclic_scc = layers[1].sccs.iter().find(|s| s.is_cyclic).unwrap();
        let singleton = layers[1].sccs.iter().find(|s| !s.is_cyclic).unwrap();
        assert_eq!(scc_names(cyclic_scc), vec!["A", "B"]);
        assert_eq!(scc_names(singleton), vec!["D"]);
    }

    #[test]
    fn scc_self_import_is_cyclic() {
        // A imports itself.
        let imports = edges(&[("A", &["A"])]);
        let layers = build_file_layers_with_sccs(&imports);

        assert_eq!(layers.len(), 1);
        assert_eq!(layers[0].sccs.len(), 1);
        assert!(layers[0].sccs[0].is_cyclic);
        assert_eq!(scc_names(&layers[0].sccs[0]), vec!["A"]);
    }

    #[test]
    fn scc_three_file_ring() {
        // A → B → C → A
        let imports = edges(&[("A", &["B"]), ("B", &["C"]), ("C", &["A"])]);
        let layers = build_file_layers_with_sccs(&imports);

        assert_eq!(layers.len(), 1);
        assert_eq!(layers[0].sccs.len(), 1);
        assert!(layers[0].sccs[0].is_cyclic);
        assert_eq!(scc_names(&layers[0].sccs[0]), vec!["A", "B", "C"]);
    }

    #[test]
    fn scc_wrapper_matches_flat_output() {
        // Verify build_file_layers produces the same flat output as before.
        let imports = edges(&[
            ("A", &["B", "C"]),
            ("B", &["A", "C"]),
            ("C", &[]),
            ("D", &["C"]),
        ]);
        let flat_layers = build_file_layers(&imports);
        let scc_layers = build_file_layers_with_sccs(&imports);

        assert_eq!(flat_layers.len(), scc_layers.len());
        for (flat, scc_layer) in flat_layers.iter().zip(scc_layers.iter()) {
            let flat_sorted = sorted_names(flat);
            let scc_flat: Vec<PathBuf> = scc_layer.all_files().cloned().collect();
            let scc_sorted = sorted_names(&scc_flat);
            assert_eq!(flat_sorted, scc_sorted);
        }
    }
}

#[cfg(test)]
mod hegel_tests {
    use super::*;
    use hegel::generators;
    use hegel::TestCase;
    use rustc_hash::FxHashSet as HashSet;

    const MAX_FILES: usize = 30;
    const MAX_EDGES: usize = 60;
    /// Edges may target files outside the project; those must be ignored.
    const MAX_EXTERNAL: usize = 5;

    fn file(i: usize) -> PathBuf {
        PathBuf::from(format!("f{i}.nix"))
    }

    fn external(i: usize) -> PathBuf {
        PathBuf::from(format!("ext{i}.nix"))
    }

    #[hegel::composite]
    fn import_graphs(tc: &TestCase) -> HashMap<PathBuf, Vec<PathBuf>> {
        let n = tc.draw(generators::integers::<usize>().max_value(MAX_FILES));
        let mut graph: HashMap<PathBuf, Vec<PathBuf>> = (0..n).map(|i| (file(i), vec![])).collect();
        if n == 0 {
            return graph;
        }
        let edges: Vec<(usize, usize)> = tc.draw(
            generators::vecs(generators::tuples!(
                generators::integers::<usize>().max_value(n - 1),
                generators::integers::<usize>().max_value(n - 1 + MAX_EXTERNAL),
            ))
            .max_size(MAX_EDGES),
        );
        for (from, to) in edges {
            let target = if to < n { file(to) } else { external(to - n) };
            graph.get_mut(&file(from)).unwrap().push(target);
        }
        graph
    }

    /// Brute-force reachability (reflexive) restricted to in-project files.
    fn reachable(graph: &HashMap<PathBuf, Vec<PathBuf>>, from: &Path) -> HashSet<PathBuf> {
        let mut seen = HashSet::default();
        let mut stack = vec![from.to_path_buf()];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            for dep in graph.get(&cur).into_iter().flatten() {
                if graph.contains_key(dep) {
                    stack.push(dep.clone());
                }
            }
        }
        seen
    }

    fn scc_index(layers: &[InferenceLayer]) -> HashMap<&PathBuf, (usize, usize)> {
        let mut idx = HashMap::default();
        for (li, layer) in layers.iter().enumerate() {
            for (si, scc) in layer.sccs.iter().enumerate() {
                for f in &scc.files {
                    idx.insert(f, (li, si));
                }
            }
        }
        idx
    }

    #[hegel::test]
    fn layers_partition_the_files(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let layers = build_file_layers_with_sccs(&graph);
        let mut seen = HashSet::default();
        for f in layers.iter().flat_map(|l| l.all_files()) {
            assert!(seen.insert(f.clone()), "{f:?} appears twice");
        }
        let expected: HashSet<PathBuf> = graph.keys().cloned().collect();
        assert_eq!(seen, expected);
    }

    #[hegel::test]
    fn same_scc_iff_mutually_reachable(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let layers = build_file_layers_with_sccs(&graph);
        let idx = scc_index(&layers);
        let reach: HashMap<&PathBuf, HashSet<PathBuf>> =
            graph.keys().map(|f| (f, reachable(&graph, f))).collect();
        for a in graph.keys() {
            for b in graph.keys() {
                let mutual = reach[a].contains(b) && reach[b].contains(a);
                assert_eq!(idx[a] == idx[b], mutual, "{a:?} {b:?}");
            }
        }
    }

    #[hegel::test]
    fn dependencies_come_in_earlier_layers(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let layers = build_file_layers_with_sccs(&graph);
        let idx = scc_index(&layers);
        for (from, deps) in &graph {
            for dep in deps.iter().filter(|d| graph.contains_key(*d)) {
                if idx[from] == idx[dep] {
                    continue;
                }
                assert!(idx[dep].0 < idx[from].0, "{dep:?} must precede {from:?}");
            }
        }
    }

    #[hegel::test]
    fn is_cyclic_matches_structure(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let layers = build_file_layers_with_sccs(&graph);
        for scc in layers.iter().flat_map(|l| l.sccs.iter()) {
            let self_import = scc.files.len() == 1 && graph[&scc.files[0]].contains(&scc.files[0]);
            assert_eq!(
                scc.is_cyclic,
                scc.files.len() > 1 || self_import,
                "{:?}",
                scc.files
            );
        }
    }

    #[hegel::test]
    fn flat_layers_match_scc_layers(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let flat = build_file_layers(&graph);
        let sccs = build_file_layers_with_sccs(&graph);
        assert_eq!(flat.len(), sccs.len());
        // Order within a layer is not part of the contract.
        for (a, b) in flat.iter().zip(&sccs) {
            let a: HashSet<&PathBuf> = a.iter().collect();
            let b: HashSet<&PathBuf> = b.all_files().collect();
            assert_eq!(a, b);
        }
    }

    #[hegel::test]
    fn importer_counts_count_in_project_edges(tc: TestCase) {
        let graph = tc.draw(import_graphs());
        let counts = compute_importer_counts(&graph);
        let mut expected: HashMap<PathBuf, usize> = HashMap::default();
        for deps in graph.values() {
            for d in deps.iter().filter(|d| graph.contains_key(*d)) {
                *expected.entry(d.clone()).or_default() += 1;
            }
        }
        assert_eq!(counts, expected);
    }
}
