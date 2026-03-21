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

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use petgraph::algo::{condensation, toposort};
use petgraph::graph::{DiGraph, NodeIndex};

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
    if file_imports.is_empty() {
        return vec![];
    }

    // =========================================================================
    // Step A: Build the raw file graph and condensation DAG
    // =========================================================================

    // Assign a graph node to every file that appears as a key in the import map.
    let mut graph: DiGraph<PathBuf, ()> = DiGraph::new();
    let mut node_map: HashMap<&Path, NodeIndex> = HashMap::new();

    for path in file_imports.keys() {
        let idx = graph.add_node(path.clone());
        node_map.insert(path.as_path(), idx);
    }

    // Add edges: importer → dependency (only for in-project targets).
    for (importer, deps) in file_imports {
        let from = node_map[importer.as_path()];
        for dep in deps {
            if let Some(&to) = node_map.get(dep.as_path()) {
                graph.add_edge(from, to, ());
            }
            // Imports to files outside the project set are silently dropped.
        }
    }

    // Condensation: compute SCCs and build a DAG where each node is a
    // Vec<PathBuf> containing the SCC's member files. `make_acyclic=true`
    // strips self-loops and duplicate edges within the condensed graph.
    let condensed = condensation(graph, true);

    // =========================================================================
    // Step B: Compute depth and group into layers
    // =========================================================================
    //
    // Walk in topological order (leaves first). Each condensed node's depth is
    // max(depth of successors) + 1 for nodes with outgoing edges, or 0 for
    // leaf nodes. We then group by depth.
    //
    // Note: petgraph's condensation reverses the node order relative to the
    // original graph, and edges point from SCCs to their dependencies. We
    // compute depth based on successors (dependencies) so that leaves get
    // depth 0 and roots get the highest depth.

    let topo_order = match toposort(&condensed, None) {
        Ok(order) => order,
        Err(_) => {
            // Should never happen on a condensation DAG, but handle gracefully:
            // return all files in a single layer.
            let all_files: Vec<PathBuf> = file_imports.keys().cloned().collect();
            return vec![all_files];
        }
    };

    let mut depth: HashMap<NodeIndex, usize> = HashMap::with_capacity(topo_order.len());

    // Process in reverse topological order so that when we process a node,
    // all its successors (dependencies) already have their depth computed.
    for &node in topo_order.iter().rev() {
        let max_dep_depth = condensed
            .neighbors(node)
            .filter_map(|succ| depth.get(&succ))
            .max()
            .copied();

        let node_depth = match max_dep_depth {
            Some(d) => d + 1,
            None => 0, // Leaf node: no in-project dependencies.
        };
        depth.insert(node, node_depth);
    }

    // Group condensed nodes by depth, then expand each to its member files.
    let max_depth = depth.values().copied().max().unwrap_or(0);
    let mut layers: Vec<Vec<PathBuf>> = vec![Vec::new(); max_depth + 1];

    for (&node, &d) in &depth {
        layers[d].extend(condensed[node].iter().cloned());
    }

    // Remove any empty layers (shouldn't happen, but defensive).
    layers.retain(|l| !l.is_empty());

    layers
}

/// Compute importer counts for reference-counted eviction.
///
/// Returns a map from each file to the number of in-project files that import
/// it. Files with 0 importers (leaves that nobody depends on) are not present
/// in the map.
pub fn compute_importer_counts(
    file_imports: &HashMap<PathBuf, Vec<PathBuf>>,
) -> HashMap<PathBuf, usize> {
    let mut counts: HashMap<PathBuf, usize> = HashMap::new();
    let project_files: std::collections::HashSet<&PathBuf> = file_imports.keys().collect();

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
                    deps.iter().map(|d| PathBuf::from(d)).collect(),
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
        let imports = HashMap::new();
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
}
