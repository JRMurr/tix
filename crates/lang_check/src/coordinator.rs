// ==============================================================================
// InferenceCoordinator: demand-driven cross-file type inference
// ==============================================================================
//
// Manages a concurrent cache of inferred file signatures (root types) and
// provides demand-driven inference: when file A imports file B, B is inferred
// first and A gets B's real type instead of ⊤.
//
// Two modes of operation:
//   - Active: `demand_file()` recursively infers a file and its transitive
//     imports. Used by the CLI for batch checking and by the LSP for resolving
//     unanalyzed dependencies.
//   - Passive: `set_signature()` / `get_signature()` for the LSP's event-driven
//     analysis loop, where files are analyzed one at a time and results cached.
//
// The coordinator does NOT own the Salsa database. Syntax extraction is
// delegated to a `SyntaxProvider` trait, which the CLI and LSP implement
// differently (pre-extracted HashMap vs Salsa-behind-Mutex).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use dashmap::DashMap;
use parking_lot::{Condvar, Mutex};
use rayon::prelude::*;

use crate::imports::{import_errors_to_diagnostics, resolve_import_types};
use crate::{run_inference, CheckResult, FileSignature, InferenceInputs, SyntaxBundle};
use lang_ty::OwnedTy;

// ==============================================================================
// SyntaxProvider trait
// ==============================================================================

/// Provides syntax-phase data for a file. The coordinator calls this to get
/// the prerequisites for inference. Implementations handle Salsa access,
/// file I/O, and context resolution.
///
/// Must be `Send + Sync` because demand-driven inference may run on rayon
/// threads concurrently.
pub trait SyntaxProvider: Send + Sync {
    /// Extract all syntax data needed for inference from a file path.
    /// Returns `None` if the file cannot be read or parsed.
    fn syntax_for_file(&self, path: &Path) -> Option<SyntaxBundle>;
}

// ==============================================================================
// FileSlot: concurrent computation tracking
// ==============================================================================

/// State of a file in the coordinator cache. Tracks whether inference is
/// in-progress (so other threads can wait) or complete.
enum FileSlot {
    /// Inference is in-progress on some thread. Other threads wait on the
    /// condvar and reuse the result when it's ready.
    Computing {
        /// Signaled when inference completes and the slot transitions to Ready.
        notify: Arc<(Mutex<bool>, Condvar)>,
    },
    /// Inference completed. The signature is `None` if inference failed or
    /// the file has no meaningful root type.
    Ready(Option<FileSignature>),
}

// ==============================================================================
// CoordinatedResult
// ==============================================================================

/// Result of a demand-driven inference for a single file.
pub struct CoordinatedResult {
    pub check_result: CheckResult,
    pub signature: Option<FileSignature>,
    /// Import paths discovered during scanning (for dependency tracking).
    pub import_paths: Vec<PathBuf>,
}

// ==============================================================================
// InferenceCoordinator
// ==============================================================================

pub struct InferenceCoordinator {
    /// Concurrent cache of file inference state.
    cache: DashMap<PathBuf, FileSlot>,

    /// Reverse dependency index: imported file → set of importers.
    /// Used for invalidation cascading.
    reverse_deps: Mutex<HashMap<PathBuf, HashSet<PathBuf>>>,

    /// Forward dependency index: importer → list of imported files.
    /// Used for O(old_import_count) cleanup when deps change.
    forward_deps: Mutex<HashMap<PathBuf, Vec<PathBuf>>>,
}

// Thread-local set of files currently being inferred on this thread.
// Used to detect import cycles (A imports B imports A) and break them
// by returning ⊤ for the back-edge.
thread_local! {
    static IN_PROGRESS: RefCell<HashSet<PathBuf>> = RefCell::new(HashSet::new());
}

impl InferenceCoordinator {
    pub fn new() -> Self {
        Self {
            cache: DashMap::new(),
            reverse_deps: Mutex::new(HashMap::new()),
            forward_deps: Mutex::new(HashMap::new()),
        }
    }

    /// Build a cache-hit result: no inference was run, just returning the
    /// previously computed signature.
    fn cached_result(sig: &Option<FileSignature>) -> CoordinatedResult {
        CoordinatedResult {
            check_result: CheckResult {
                inference: None,
                diagnostics: vec![],
                timed_out: false,
            },
            signature: sig.clone(),
            import_paths: vec![],
        }
    }

    // =========================================================================
    // Active mode: demand-driven inference
    // =========================================================================

    /// Infer a file and all its transitive imports on demand.
    ///
    /// If the file is already cached, returns the cached signature immediately.
    /// If another thread is computing the same file, blocks and waits for the
    /// result. Import cycles on the same thread are detected and broken with ⊤.
    ///
    /// **Blocking behavior:** When waiting for another thread, this blocks the
    /// current rayon worker on a Condvar. Deep import chains (A→B→C→D→...)
    /// serialize inference for those files, and each blocked worker is
    /// unavailable for other rayon work items. The thread pool must be larger
    /// than the maximum import chain depth to avoid starvation. In batch mode
    /// this is mitigated by the typically flat structure of most Nix projects.
    pub fn demand_file(
        &self,
        path: &Path,
        syntax_provider: &dyn SyntaxProvider,
        cancel_flag: Option<Arc<AtomicBool>>,
    ) -> Option<CoordinatedResult> {
        // Fast path: already computed.
        if let Some(entry) = self.cache.get(path) {
            if let FileSlot::Ready(ref sig) = *entry {
                return Some(Self::cached_result(sig));
            }
        }

        // Cycle detection: if this thread is already inferring this file,
        // we have an import cycle. Return None (maps to ⊤ in the importer).
        let is_cycle = IN_PROGRESS.with(|s| !s.borrow_mut().insert(path.to_path_buf()));
        if is_cycle {
            return None;
        }

        // Try to claim this file for computation. If another thread is
        // already computing it, wait for the result.
        let notify = Arc::new((Mutex::new(false), Condvar::new()));
        let should_compute = {
            let entry =
                self.cache
                    .entry(path.to_path_buf())
                    .or_insert_with(|| FileSlot::Computing {
                        notify: Arc::clone(&notify),
                    });

            match &*entry {
                FileSlot::Ready(sig) => {
                    // Another thread finished between our check and entry.
                    let result = Self::cached_result(sig);
                    IN_PROGRESS.with(|s| s.borrow_mut().remove(path));
                    return Some(result);
                }
                FileSlot::Computing {
                    notify: existing_notify,
                } => {
                    // Check if this is our own notify (we just inserted it)
                    // or another thread's.
                    if Arc::ptr_eq(existing_notify, &notify) {
                        // We inserted it — we should compute.
                        true
                    } else {
                        // Another thread is computing. Wait on their notify.
                        let their_notify = Arc::clone(existing_notify);
                        drop(entry);
                        let (lock, cvar) = &*their_notify;
                        let mut done = lock.lock();
                        while !*done {
                            cvar.wait(&mut done);
                        }
                        // Now the result should be in the cache.
                        IN_PROGRESS.with(|s| s.borrow_mut().remove(path));
                        if let Some(entry) = self.cache.get(path) {
                            if let FileSlot::Ready(ref sig) = *entry {
                                return Some(Self::cached_result(sig));
                            }
                        }
                        return None;
                    }
                }
            }
        };

        if !should_compute {
            IN_PROGRESS.with(|s| s.borrow_mut().remove(path));
            return None;
        }

        // Actually compute: extract syntax, resolve imports, run inference.
        let result = self.compute_file(path, syntax_provider, cancel_flag);

        // Store result and notify waiters.
        // Only cache successful results — failed files (provider returned None)
        // should not be cached permanently, since the file may become available
        // later (e.g. created on disk, or temporarily unreadable).
        match &result {
            Some(r) => {
                self.cache
                    .insert(path.to_path_buf(), FileSlot::Ready(r.signature.clone()));
            }
            None => {
                self.cache.remove(path);
            }
        }
        let (lock, cvar) = &*notify;
        *lock.lock() = true;
        cvar.notify_all();

        IN_PROGRESS.with(|s| s.borrow_mut().remove(path));
        result
    }

    /// Batch inference: infer all files in parallel with demand-driven import
    /// resolution. Returns results in the same order as the input files.
    pub fn demand_batch(
        &self,
        files: &[PathBuf],
        syntax_provider: &dyn SyntaxProvider,
    ) -> Vec<(PathBuf, Option<CoordinatedResult>)> {
        files
            .par_iter()
            .map(|path| {
                let result = self.demand_file(path, syntax_provider, None);
                (path.clone(), result)
            })
            .collect()
    }

    /// The core computation: extract syntax, scan imports, demand dependencies,
    /// build InferenceInputs, run inference, extract signature.
    fn compute_file(
        &self,
        path: &Path,
        syntax_provider: &dyn SyntaxProvider,
        cancel_flag: Option<Arc<AtomicBool>>,
    ) -> Option<CoordinatedResult> {
        let bundle = syntax_provider.syntax_for_file(path)?;

        let base_dir = path.parent().unwrap_or(Path::new("/"));

        // Scan for imports and demand each dependency's type from the cache.
        // Dependencies that aren't cached yet are inferred recursively.
        let import_resolution =
            resolve_import_types(&bundle.module, &bundle.name_res, base_dir, |dep_path| {
                // Try the cache first (fast path).
                if let Some(sig) = self.get_signature(dep_path) {
                    return Some(sig);
                }
                // Demand-driven: infer the dependency.
                let dep_result =
                    self.demand_file(dep_path, syntax_provider, cancel_flag.clone())?;
                dep_result.signature.map(|s| s.root_ty)
            });

        let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

        // Use the resolved paths from import resolution (already computed during
        // scanning) instead of re-scanning the AST.
        let import_paths = import_resolution.resolved_paths;

        // Record dependencies for invalidation.
        self.record_deps(path, &import_paths);

        // Build InferenceInputs and run inference.
        let inputs = InferenceInputs {
            module: bundle.module,
            module_indices: bundle.module_indices,
            name_res: bundle.name_res,
            grouped_defs: bundle.grouped_defs,
            registry: bundle.registry,
            import_types: import_resolution.types,
            import_diagnostics,
            context_args: bundle.context_args,
            deadline_secs: bundle.deadline_secs,
            rss_limit_mb: None,
        };

        let check_result = run_inference(&inputs, cancel_flag);

        // Extract root type as the file's signature.
        let signature = check_result.inference.as_ref().and_then(|inf| {
            let root_ref = inf.expr_ty_map.get(inputs.module.entry_expr).copied()?;
            let owned = OwnedTy::new(inf.arena.clone(), root_ref).compact();
            Some(FileSignature { root_ty: owned })
        });

        Some(CoordinatedResult {
            check_result,
            signature,
            import_paths,
        })
    }

    // =========================================================================
    // Passive mode: cache read/write for LSP event-driven analysis
    // =========================================================================

    /// Get the cached root type for a file, if available.
    pub fn get_signature(&self, path: &Path) -> Option<OwnedTy> {
        self.cache.get(path).and_then(|entry| match &*entry {
            FileSlot::Ready(Some(sig)) => Some(sig.root_ty.clone()),
            _ => None,
        })
    }

    /// Store a file's signature in the cache (passive mode).
    /// Returns `true` if the signature changed (callers use this to decide
    /// whether to trigger dependent re-analysis).
    pub fn set_signature(&self, path: &Path, sig: FileSignature) -> bool {
        let changed = self
            .cache
            .get(path)
            .map(|entry| match &*entry {
                FileSlot::Ready(Some(existing)) => *existing != sig,
                _ => true,
            })
            .unwrap_or(true);

        if changed {
            self.cache
                .insert(path.to_path_buf(), FileSlot::Ready(Some(sig)));
        }
        changed
    }

    /// Resolve import types for a module using the coordinator's cache.
    /// Used by the LSP's Phase B as a drop-in for `resolve_import_types_from_stubs`.
    pub fn resolve_imports(
        &self,
        module: &lang_ast::Module,
        name_res: &lang_ast::NameResolution,
        base_dir: &Path,
    ) -> crate::imports::ImportResolution {
        resolve_import_types(module, name_res, base_dir, |p| self.get_signature(p))
    }

    // =========================================================================
    // Dependency tracking & invalidation
    // =========================================================================

    /// Record the import dependencies for a file. Replaces any previous entries.
    pub fn record_deps(&self, importer: &Path, imported: &[PathBuf]) {
        let mut reverse = self.reverse_deps.lock();
        let mut forward = self.forward_deps.lock();

        // Remove old entries using the forward index.
        if let Some(old_deps) = forward.remove(importer) {
            for dep in &old_deps {
                if let Some(set) = reverse.get_mut(dep) {
                    set.remove(importer);
                }
            }
        }

        // Insert new entries.
        for dep in imported {
            reverse
                .entry(dep.clone())
                .or_default()
                .insert(importer.to_path_buf());
        }
        forward.insert(importer.to_path_buf(), imported.to_vec());
    }

    /// Invalidate a file and all its transitive dependents. Returns the list
    /// of paths that were evicted (excluding the root path itself).
    pub fn invalidate(&self, path: &Path) -> Vec<PathBuf> {
        let mut evicted = Vec::new();
        let mut visited = HashSet::new();
        // Snapshot reverse_deps once to avoid multiple lock acquisitions
        // during recursion and to prevent TOCTOU races with concurrent
        // cache modifications.
        let reverse_deps = self.reverse_deps.lock().clone();
        self.invalidate_inner(path, &reverse_deps, &mut visited, &mut evicted);
        evicted
    }

    fn invalidate_inner(
        &self,
        path: &Path,
        reverse_deps: &HashMap<PathBuf, HashSet<PathBuf>>,
        visited: &mut HashSet<PathBuf>,
        evicted: &mut Vec<PathBuf>,
    ) {
        if !visited.insert(path.to_path_buf()) {
            return;
        }
        self.cache.remove(path);
        if let Some(dependents) = reverse_deps.get(path) {
            for dep in dependents {
                evicted.push(dep.clone());
                self.invalidate_inner(dep, reverse_deps, visited, evicted);
            }
        }
    }

    /// Return the set of files that import the given path.
    pub fn get_dependents(&self, path: &Path) -> Vec<PathBuf> {
        self.reverse_deps
            .lock()
            .get(path)
            .map(|set| set.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Remove signatures for a batch of files. Used by the CLI's
    /// reference-counted eviction to drop signatures whose importers
    /// have all been processed.
    pub fn remove_signatures_batch(&self, paths: &[PathBuf]) {
        for path in paths {
            self.cache.remove(path.as_path());
        }
    }

    /// Remove a file's signature and return its dependents (for didClose).
    pub fn remove_signature(&self, path: &Path) -> Vec<PathBuf> {
        self.cache.remove(path);
        self.get_dependents(path)
    }

    /// Clear all cached state (used on registry reload).
    pub fn clear(&self) {
        self.cache.clear();
        self.reverse_deps.lock().clear();
        self.forward_deps.lock().clear();
    }
}

impl Default for InferenceCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aliases::TypeAliasRegistry;
    use lang_ty::{OutputTy, TypeArena};
    use std::io::Write;

    /// Helper: create a FileSignature from an OutputTy value.
    fn make_sig(ty: OutputTy) -> FileSignature {
        let mut arena = TypeArena::new();
        let root = arena.intern(ty);
        FileSignature {
            root_ty: OwnedTy::new(Arc::new(arena), root),
        }
    }

    /// Helper: compare an OwnedTy to an OutputTy structurally.
    fn owned_ty_eq(owned: &OwnedTy, expected: &OutputTy) -> bool {
        owned.get() == expected
    }

    /// A test syntax provider that reads .nix files from disk and parses them
    /// via a shared RootDatabase.
    struct TestSyntaxProvider {
        db: Mutex<lang_ast::RootDatabase>,
        registry: Arc<TypeAliasRegistry>,
    }

    impl TestSyntaxProvider {
        fn new() -> Self {
            Self {
                db: Mutex::new(lang_ast::RootDatabase::default()),
                registry: Arc::new(TypeAliasRegistry::default()),
            }
        }
    }

    impl SyntaxProvider for TestSyntaxProvider {
        fn syntax_for_file(&self, path: &Path) -> Option<SyntaxBundle> {
            let db = self.db.lock();
            let nix_file = db.read_file(path.to_path_buf()).ok()?;
            let (module, _source_map) = lang_ast::module_and_source_maps(&*db, nix_file);
            let module_indices = lang_ast::module_indices(&*db, nix_file);
            let name_res = lang_ast::name_resolution(&*db, nix_file);
            let grouped_defs = lang_ast::group_def(&*db, nix_file);
            Some(SyntaxBundle {
                path: path.to_path_buf(),
                module,
                module_indices,
                name_res,
                grouped_defs,
                registry: Arc::clone(&self.registry),
                context_args: Arc::default(),
                deadline_secs: Some(10),
            })
        }
    }

    /// Helper: write a temp .nix file and return its canonical path.
    fn write_nix(dir: &Path, name: &str, contents: &str) -> PathBuf {
        let path = dir.join(name);
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(contents.as_bytes()).unwrap();
        path.canonicalize().unwrap()
    }

    #[test]
    fn passive_set_get_roundtrip() {
        let coord = InferenceCoordinator::new();
        let path = PathBuf::from("/tmp/test_passive.nix");
        let sig = make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int));

        assert!(coord.get_signature(&path).is_none());
        coord.set_signature(&path, sig);
        let retrieved = coord.get_signature(&path);
        assert!(retrieved.is_some());
        assert!(owned_ty_eq(
            &retrieved.unwrap(),
            &OutputTy::Primitive(lang_ty::PrimitiveTy::Int)
        ));
    }

    #[test]
    fn set_signature_returns_changed() {
        let coord = InferenceCoordinator::new();
        let path = PathBuf::from("/tmp/test_changed.nix");
        let sig_int = make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int));
        let sig_str = make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::String));

        // Clone shares the same Arc, so PartialEq (ptr-based) will match.
        let sig_int_clone = sig_int.clone();
        assert!(coord.set_signature(&path, sig_int));
        assert!(!coord.set_signature(&path, sig_int_clone));
        assert!(coord.set_signature(&path, sig_str));
    }

    #[test]
    fn invalidation_cascades() {
        let coord = InferenceCoordinator::new();
        let a = PathBuf::from("/a.nix");
        let b = PathBuf::from("/b.nix");
        let c = PathBuf::from("/c.nix");

        // a imports b, b imports c
        coord.set_signature(&a, make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)));
        coord.set_signature(&b, make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)));
        coord.set_signature(&c, make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)));
        coord.record_deps(&a, &[b.clone()]);
        coord.record_deps(&b, &[c.clone()]);

        // Invalidate c → should cascade to b and a.
        let evicted = coord.invalidate(&c);
        assert!(evicted.contains(&b));
        assert!(evicted.contains(&a));
        assert!(coord.get_signature(&a).is_none());
        assert!(coord.get_signature(&b).is_none());
        assert!(coord.get_signature(&c).is_none());
    }

    #[test]
    fn demand_file_simple() {
        let dir = tempfile::tempdir().unwrap();
        let b_path = write_nix(dir.path(), "b.nix", "42");
        let a_contents = format!("import {}", b_path.display());
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        let result = coord.demand_file(&a_path, &provider, None);
        assert!(result.is_some());

        // b should now be cached.
        assert!(coord.get_signature(&b_path).is_some());
    }

    #[test]
    fn demand_file_cycle_detection() {
        let dir = tempfile::tempdir().unwrap();

        // Create a cycle: a.nix imports b.nix, b.nix imports a.nix.
        let a_path = dir.path().join("a.nix");
        let b_path = dir.path().join("b.nix");

        // Write b first so we can reference its path in a.
        std::fs::write(&b_path, format!("import {}", a_path.display())).unwrap();
        std::fs::write(&a_path, format!("import {}", b_path.display())).unwrap();

        let a_path = a_path.canonicalize().unwrap();
        let _b_path = b_path.canonicalize().unwrap();

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // Should not deadlock — cycle is broken with ⊤.
        let result = coord.demand_file(&a_path, &provider, None);
        assert!(result.is_some());
        // Both files should be cached (even if one got ⊤ for the back-edge).
        assert!(coord.get_signature(&a_path).is_some() || coord.cache.contains_key(&a_path));
    }

    #[test]
    fn demand_batch_parallel() {
        let dir = tempfile::tempdir().unwrap();
        let a_path = write_nix(dir.path(), "a.nix", "1");
        let b_path = write_nix(dir.path(), "b.nix", "2");
        let c_path = write_nix(dir.path(), "c.nix", "3");

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        let results = coord.demand_batch(&[a_path, b_path, c_path], &provider);
        assert_eq!(results.len(), 3);
        for (_, result) in &results {
            assert!(result.is_some());
        }
    }

    #[test]
    fn diamond_dependency() {
        let dir = tempfile::tempdir().unwrap();

        // d.nix is the shared dependency
        let d_path = write_nix(dir.path(), "d.nix", "42");

        // b.nix and c.nix both import d.nix
        let b_contents = format!("import {}", d_path.display());
        let b_path = write_nix(dir.path(), "b.nix", &b_contents);
        let c_contents = format!("import {}", d_path.display());
        let c_path = write_nix(dir.path(), "c.nix", &c_contents);

        // a.nix imports both b.nix and c.nix
        let a_contents = format!(
            "let b = import {}; c = import {}; in {{ inherit b c; }}",
            b_path.display(),
            c_path.display()
        );
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        let result = coord.demand_file(&a_path, &provider, None);
        assert!(result.is_some());

        // All four files should be cached.
        assert!(coord.get_signature(&a_path).is_some());
        assert!(coord.get_signature(&b_path).is_some());
        assert!(coord.get_signature(&c_path).is_some());
        assert!(coord.get_signature(&d_path).is_some());
    }

    #[test]
    fn clear_resets_everything() {
        let coord = InferenceCoordinator::new();
        let path = PathBuf::from("/tmp/test_clear.nix");
        coord.set_signature(
            &path,
            make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)),
        );
        coord.record_deps(&path, &[PathBuf::from("/tmp/dep.nix")]);

        coord.clear();
        assert!(coord.get_signature(&path).is_none());
        assert!(coord.get_dependents(&path).is_empty());
    }

    /// Regression: invalidation with cycles in the reverse_deps graph must
    /// not loop infinitely. The visited set (W1) prevents re-entering nodes.
    #[test]
    fn invalidation_with_cycle_in_deps() {
        let coord = InferenceCoordinator::new();
        let a = PathBuf::from("/cycle_a.nix");
        let b = PathBuf::from("/cycle_b.nix");

        coord.set_signature(&a, make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)));
        coord.set_signature(&b, make_sig(OutputTy::Primitive(lang_ty::PrimitiveTy::Int)));

        // Create a cycle: a→b and b→a in reverse deps.
        coord.record_deps(&a, &[b.clone()]);
        coord.record_deps(&b, &[a.clone()]);

        // Should not infinite-loop.
        let evicted = coord.invalidate(&a);
        // b should be evicted (it depends on a).
        assert!(evicted.contains(&b));
        assert!(coord.get_signature(&a).is_none());
        assert!(coord.get_signature(&b).is_none());
    }

    /// After invalidating a dependency and re-demanding the importer, the
    /// importer should be re-inferred with fresh dependency types.
    #[test]
    fn invalidation_then_re_demand() {
        let dir = tempfile::tempdir().unwrap();
        let b_path = write_nix(dir.path(), "b.nix", "42");
        let a_contents = format!("import {}", b_path.display());
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // First demand: infer A (which imports B).
        let result = coord.demand_file(&a_path, &provider, None);
        assert!(result.is_some());
        assert!(coord.get_signature(&b_path).is_some());

        // Invalidate B → should cascade to A.
        let evicted = coord.invalidate(&b_path);
        assert!(evicted.contains(&a_path));
        assert!(coord.get_signature(&a_path).is_none());
        assert!(coord.get_signature(&b_path).is_none());

        // Re-demand A → should re-infer with fresh B.
        let result2 = coord.demand_file(&a_path, &provider, None);
        assert!(result2.is_some());
        assert!(coord.get_signature(&b_path).is_some());
    }

    /// Two threads demanding the same file concurrently: exactly one computes,
    /// the other waits. Both should get a valid result.
    #[test]
    fn concurrent_demand_same_file() {
        let dir = tempfile::tempdir().unwrap();
        let a_path = write_nix(dir.path(), "a.nix", "1 + 2");

        let provider = Arc::new(TestSyntaxProvider::new());
        let coord = Arc::new(InferenceCoordinator::new());

        let coord1 = Arc::clone(&coord);
        let coord2 = Arc::clone(&coord);
        let provider1 = Arc::clone(&provider);
        let provider2 = Arc::clone(&provider);
        let path1 = a_path.clone();
        let path2 = a_path.clone();

        let t1 = std::thread::spawn(move || coord1.demand_file(&path1, &*provider1, None));
        let t2 = std::thread::spawn(move || coord2.demand_file(&path2, &*provider2, None));

        let r1 = t1.join().unwrap();
        let r2 = t2.join().unwrap();

        // Both threads should get a result.
        assert!(r1.is_some());
        assert!(r2.is_some());
    }

    /// When the syntax provider returns None for a file in an import chain,
    /// the importer should still get a result (the unavailable import maps to ⊤).
    #[test]
    fn provider_returns_none_mid_chain() {
        let dir = tempfile::tempdir().unwrap();

        // Create a.nix that imports a nonexistent path — the provider will
        // return None for the missing dependency.
        let missing = dir.path().join("nonexistent.nix");
        let a_contents = format!("import {}", missing.display());
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // Should still produce a result for a.nix despite the missing dep.
        let result = coord.demand_file(&a_path, &provider, None);
        assert!(result.is_some());
    }

    /// Failed files (provider returns None) should not be cached permanently,
    /// allowing re-inference when the file becomes available.
    #[test]
    fn failed_file_not_cached() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("missing.nix");

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // File doesn't exist → provider returns None.
        let result = coord.demand_file(&path, &provider, None);
        assert!(result.is_none());

        // Should NOT be cached as Ready(None).
        assert!(!coord.cache.contains_key(&path));
    }

    // =========================================================================
    // Layered inference integration tests
    // =========================================================================

    /// End-to-end test: cross-file type flow via layered inference.
    /// b.nix = 42, a.nix = import ./b.nix → a.nix should get type `int`.
    #[test]
    fn layered_cross_file_type_flow() {
        use crate::file_graph;

        let dir = tempfile::tempdir().unwrap();
        let b_path = write_nix(dir.path(), "b.nix", "42");
        let a_contents = format!("import {}", b_path.display());
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        // Build the import edge map.
        let mut import_edges = HashMap::new();
        import_edges.insert(a_path.clone(), vec![b_path.clone()]);
        import_edges.insert(b_path.clone(), vec![]);

        // Build layers.
        let layers = file_graph::build_file_layers(&import_edges);
        assert_eq!(layers.len(), 2);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // Infer layer by layer.
        for layer in &layers {
            for path in layer {
                let result = coord
                    .demand_file(path, &provider, None)
                    .expect("inference should succeed");

                // Cache the signature for subsequent layers.
                if let Some(sig) = result.signature {
                    coord.set_signature(path, sig);
                }
            }
        }

        // a.nix should have type `int` (from b.nix), not ⊤.
        let a_ty = coord
            .get_signature(&a_path)
            .expect("a.nix should be cached");
        assert!(owned_ty_eq(
            &a_ty,
            &OutputTy::Primitive(lang_ty::PrimitiveTy::Int)
        ));
    }

    /// Diamond dependency: shared dep inferred once, type flows correctly
    /// through both paths.
    #[test]
    fn layered_diamond_dependency() {
        use crate::file_graph;

        let dir = tempfile::tempdir().unwrap();
        let d_path = write_nix(dir.path(), "d.nix", "\"hello\"");
        let b_contents = format!("import {}", d_path.display());
        let b_path = write_nix(dir.path(), "b.nix", &b_contents);
        let c_contents = format!("import {}", d_path.display());
        let c_path = write_nix(dir.path(), "c.nix", &c_contents);
        let a_contents = format!(
            "let b = import {}; c = import {}; in {{ inherit b c; }}",
            b_path.display(),
            c_path.display()
        );
        let a_path = write_nix(dir.path(), "a.nix", &a_contents);

        let mut import_edges = HashMap::new();
        import_edges.insert(d_path.clone(), vec![]);
        import_edges.insert(b_path.clone(), vec![d_path.clone()]);
        import_edges.insert(c_path.clone(), vec![d_path.clone()]);
        import_edges.insert(a_path.clone(), vec![b_path.clone(), c_path.clone()]);

        let layers = file_graph::build_file_layers(&import_edges);
        assert_eq!(layers.len(), 3);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        for layer in &layers {
            layer.iter().for_each(|path| {
                let result = coord
                    .demand_file(path, &provider, None)
                    .expect("inference should succeed");
                if let Some(sig) = result.signature {
                    coord.set_signature(path, sig);
                }
            });
        }

        // b.nix and c.nix should both be `string` (from d.nix).
        let b_ty = coord.get_signature(&b_path).expect("b.nix cached");
        assert!(owned_ty_eq(
            &b_ty,
            &OutputTy::Primitive(lang_ty::PrimitiveTy::String)
        ));
        let c_ty = coord.get_signature(&c_path).expect("c.nix cached");
        assert!(owned_ty_eq(
            &c_ty,
            &OutputTy::Primitive(lang_ty::PrimitiveTy::String)
        ));
    }

    /// Cycle: A ↔ B doesn't deadlock. Files complete with ⊤ for back-edges.
    #[test]
    fn layered_cycle_no_deadlock() {
        use crate::file_graph;

        let dir = tempfile::tempdir().unwrap();
        let a_path_raw = dir.path().join("a.nix");
        let b_path_raw = dir.path().join("b.nix");

        std::fs::write(&b_path_raw, format!("import {}", a_path_raw.display())).unwrap();
        std::fs::write(&a_path_raw, format!("import {}", b_path_raw.display())).unwrap();

        let a_path = a_path_raw.canonicalize().unwrap();
        let b_path = b_path_raw.canonicalize().unwrap();

        let mut import_edges = HashMap::new();
        import_edges.insert(a_path.clone(), vec![b_path.clone()]);
        import_edges.insert(b_path.clone(), vec![a_path.clone()]);

        let layers = file_graph::build_file_layers(&import_edges);
        // Both should be in the same SCC layer.
        assert_eq!(layers.len(), 1);
        assert_eq!(layers[0].len(), 2);

        let provider = TestSyntaxProvider::new();
        let coord = InferenceCoordinator::new();

        // Should not deadlock.
        for path in &layers[0] {
            let result = coord.demand_file(path, &provider, None);
            assert!(
                result.is_some(),
                "inference should succeed for {}",
                path.display()
            );
            if let Some(r) = result {
                if let Some(sig) = r.signature {
                    coord.set_signature(path, sig);
                }
            }
        }
    }
}
