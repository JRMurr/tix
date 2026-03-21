// ==============================================================================
// tower-lsp LanguageServer implementation
// ==============================================================================
//
// Lifecycle (initialize/shutdown) and request dispatch. Analysis runs inside
// spawn_blocking because rnix::Root is !Send + !Sync. The AnalysisState is
// behind a parking_lot::Mutex and all access happens within the blocking task.
//
// Event coalescing (inspired by rust-analyzer): didChange/didOpen notifications
// are cheap — they just send an event to a single analysis loop. The loop
// drains all pending events via try_recv() before starting analysis, naturally
// coalescing rapid edits without a per-file timer. Diagnostic publication is
// deferred until quiescence (no new edits for DIAGNOSTIC_QUIESCENCE_MS),
// preventing flicker during rapid typing. Analysis results are available to
// interactive requests (hover, completion) immediately.
//
// Cancellation: when a new edit arrives for a file that's currently being
// analyzed, the analysis loop checks the cancel flag between phases so it
// can re-coalesce edits without waiting for inference to complete.

use std::collections::HashMap;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use dashmap::DashMap;
use parking_lot::Mutex;
use rowan::ast::AstNode;
use tokio::sync::mpsc;

use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::config::{DiagnosticsConfig, TixConfig};
use crate::state::{AnalysisState, FileSnapshot, InferenceData};

/// Quiescence delay for diagnostic publication. Diagnostics are held back
/// until no new edits arrive for this duration, preventing flickering during
/// rapid typing. Analysis results are available to interactive requests
/// (hover, completion) immediately — only diagnostic *publication* is deferred.
const DIAGNOSTIC_QUIESCENCE_MS: u64 = 200;

/// Events sent to the single analysis loop. Mirrors rust-analyzer's closed
/// Event enum pattern — all inputs to the loop are a single enum over one
/// channel.
enum AnalysisEvent {
    /// File contents changed (didChange or didOpen).
    FileChanged {
        path: PathBuf,
        text: String,
        /// LSP document version from the editor. `None` for background-queue
        /// files that aren't open. Used in `publishDiagnostics` so editors
        /// that check versions (e.g. Helix) don't discard fresh diagnostics.
        version: Option<i32>,
    },
    /// File closed (didClose). Clears pending diagnostics for this file.
    FileClosed { path: PathBuf },
    /// Re-analyze a file because one of its imports' ephemeral stub changed.
    ReanalyzeFile { path: PathBuf },
    /// Batch warmup completed. Carry results for the analysis loop to merge.
    WarmupComplete {
        results: Vec<crate::warmup::WarmupFileResult>,
    },
}

pub struct TixLanguageServer {
    client: Client,
    state: Arc<Mutex<AnalysisState>>,
    config: Mutex<TixConfig>,
    /// Channel to the single analysis loop (like RA's VFS channel).
    event_tx: mpsc::UnboundedSender<AnalysisEvent>,
    /// Shared cancel flag. `schedule_analysis()` / `did_close()` set this to
    /// true; the analysis loop resets it to false at the start of each batch.
    /// The same flag is passed to inference, which checks it periodically via
    /// `check_limits()`.
    cancel_flag: Arc<AtomicBool>,
    /// Latest document text received via didChange/didOpen, stored immediately
    /// so completion can re-parse on the fly while analysis catches up.
    /// Cleared once analysis catches up.
    pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
    /// Lock-free per-file snapshots for handler access. The analysis loop
    /// writes SyntaxData immediately after syntax analysis, then adds
    /// InferenceData after type inference completes. Handlers read from
    /// this without ever locking the analysis mutex.
    snapshots: Arc<DashMap<PathBuf, FileSnapshot>>,
    /// Shared diagnostics config — the analysis loop reads this to determine
    /// what diagnostics to emit. Updated by `did_change_configuration`.
    diag_config: Arc<Mutex<DiagnosticsConfig>>,
    /// Shared syntax provider for demand-driven import resolution. Shared so
    /// `initialize()` can update its project config after discovering tix.toml.
    syntax_provider: Arc<crate::state::LspSyntaxProvider>,
}

impl TixLanguageServer {
    pub fn new(client: Client, registry: TypeAliasRegistry, rss_limit_mb: Option<f64>) -> Self {
        // Initialize rayon's global thread pool with 16 MB stacks, matching the
        // CLI. Deep recursion on large files needs this to avoid stack overflow.
        rayon::ThreadPoolBuilder::new()
            .stack_size(16 * 1024 * 1024)
            .build_global()
            .ok(); // Ignored if pool already initialized.

        let (event_tx, event_rx) = mpsc::unbounded_channel();
        let mut analysis_state = AnalysisState::new(registry);
        analysis_state.rss_limit_mb = rss_limit_mb;

        // Clone the coordinator Arc before moving analysis_state into the Mutex.
        // The analysis loop uses it outside the state lock for demand-driven
        // import resolution.
        let coordinator = Arc::clone(&analysis_state.coordinator);

        let syntax_provider = Arc::new(crate::state::LspSyntaxProvider::new(Arc::clone(
            &analysis_state.registry,
        )));

        let state = Arc::new(Mutex::new(analysis_state));
        let pending_text = Arc::new(Mutex::new(HashMap::new()));
        let cancel_flag = Arc::new(AtomicBool::new(false));
        let snapshots = Arc::new(DashMap::new());
        let diag_config = Arc::new(Mutex::new(DiagnosticsConfig::default()));

        // Spawn the analysis loop eagerly. Diagnostics default to enabled;
        // if the editor sends a different config via initializationOptions
        // before opening files, it takes effect before any analysis runs.
        spawn_analysis_loop(
            event_rx,
            event_tx.clone(),
            state.clone(),
            client.clone(),
            pending_text.clone(),
            cancel_flag.clone(),
            snapshots.clone(),
            diag_config.clone(),
            coordinator,
            syntax_provider.clone(),
        );

        Self {
            client,
            state,
            config: Mutex::new(TixConfig::default()),
            event_tx,
            cancel_flag,
            pending_text,
            snapshots,
            diag_config,
            syntax_provider,
        }
    }

    /// Schedule analysis for a file. The text is stored immediately in
    /// `pending_text` so that request handlers (e.g. completion) can re-parse
    /// it on the fly, then an event is sent to the analysis loop which will
    /// coalesce it with any other pending edits.
    fn schedule_analysis(&self, uri: Url, text: String, version: Option<i32>) {
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return,
        };

        // Store latest text immediately (completion can use it right away).
        self.pending_text.lock().insert(path.clone(), text.clone());

        // Cancel any in-flight analysis (like RA's trigger_cancellation()).
        self.cancel_flag.store(true, Ordering::Relaxed);

        // Send to analysis loop — it will drain and coalesce.
        self.event_tx
            .send(AnalysisEvent::FileChanged {
                path,
                text,
                version,
            })
            .ok();
    }

    /// Read from the DashMap snapshot. The callback receives the FileSnapshot
    /// and the parsed rnix Root. Returns `ContentModified` if the file hasn't
    /// been analyzed yet (no snapshot available).
    fn with_snapshot<T>(
        &self,
        uri: &Url,
        f: impl FnOnce(&FileSnapshot, &rnix::Root) -> Option<T>,
    ) -> Result<Option<T>> {
        let path = match uri_to_path(uri) {
            Some(p) => p,
            None => return Ok(None),
        };
        let snap_ref = match self.snapshots.get(&path) {
            Some(s) => s,
            None => return Err(content_modified_error()),
        };
        let root = snap_ref.syntax.parsed.tree();
        Ok(f(&snap_ref, &root))
    }

    /// Build a fresh TypeAliasRegistry from editor-provided stubs.
    ///
    /// Built-in nixpkgs stubs are always loaded. Additional stubs from
    /// editor settings (`nix.serverSettings.stubs`) are layered on top.
    /// Project-level stubs from `tix.toml` are loaded separately during
    /// `initialize()`.
    fn build_registry(&self, config: &TixConfig) -> TypeAliasRegistry {
        let mut registry = TypeAliasRegistry::with_builtins();

        // Allow overriding built-in context stubs via env var.
        if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
            log::info!("TIX_BUILTIN_STUBS override: {dir}");
            registry.set_builtin_stubs_dir(PathBuf::from(dir));
        }

        // Editor-provided stubs (from nix.serverSettings.stubs).
        for stub_path in &config.stubs {
            if let Err(e) = crate::load_stubs(&mut registry, stub_path) {
                log::warn!(
                    "Failed to load config stubs from {}: {e}",
                    stub_path.display()
                );
            }
        }

        if let Err(cycles) = registry.validate() {
            log::warn!("Cyclic type aliases detected: {:?}", cycles);
        }

        registry
    }
}

/// Single analysis loop task (like rust-analyzer's `GlobalState::run()`).
///
/// Receives `AnalysisEvent`s from `schedule_analysis` / `did_close` and
/// processes them in batches. Key design properties:
///
/// - **Event coalescing**: after receiving the first event, drains all pending
///   events via `try_recv()`. With FULL document sync, only the latest text
///   per file matters, so rapid edits naturally collapse into a single analysis.
///
/// - **Diagnostic quiescence**: diagnostics are not published immediately after
///   analysis. Instead they're buffered behind a timer. If new edits arrive
///   before the timer fires, the stale diagnostics are discarded and the timer
///   resets. This prevents flickering during rapid typing.
///
/// - **Inter-file cancellation**: between analyzing files in a batch, the loop
///   checks whether new events have arrived. If so, it cancels the current
///   batch and re-enters the drain phase to coalesce the new edits.
#[allow(clippy::too_many_arguments)]
fn spawn_analysis_loop(
    mut rx: mpsc::UnboundedReceiver<AnalysisEvent>,
    event_tx: mpsc::UnboundedSender<AnalysisEvent>,
    state: Arc<Mutex<AnalysisState>>,
    client: Client,
    pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
    cancel_flag: Arc<AtomicBool>,
    _snapshots: Arc<DashMap<PathBuf, FileSnapshot>>,
    diag_config: Arc<Mutex<DiagnosticsConfig>>,
    coordinator: Arc<lang_check::coordinator::InferenceCoordinator>,
    lsp_syntax_provider: Arc<crate::state::LspSyntaxProvider>,
) {
    tokio::spawn(async move {
        // Pending diagnostics waiting for quiescence, keyed by path.
        let mut pending_diags: HashMap<PathBuf, Vec<Diagnostic>> = HashMap::new();
        let mut diag_timer: Option<Pin<Box<tokio::time::Sleep>>> = None;
        // Track the latest document version per file. Used when publishing
        // diagnostics so editors that check versions (e.g. Helix) don't
        // discard fresh diagnostics for open files.
        let mut file_versions: HashMap<PathBuf, i32> = HashMap::new();

        loop {
            // ── Phase 1: Wait for event or diagnostic timer ──
            //
            // Like RA's select! in next_event(): block until something happens.
            // If we have pending diagnostics, race the quiescence timer against
            // new events. New events reset the timer (like RA discards stale
            // diagnostics when state changes).
            let first_event: Option<AnalysisEvent> = if let Some(ref mut timer) = diag_timer {
                tokio::select! {
                    _ = &mut *timer => {
                        // Quiescence reached — publish all pending diagnostics.
                        for (path, diags) in pending_diags.drain() {
                            if let Ok(uri) = Url::from_file_path(&path) {
                                let version = file_versions.get(&path).copied();
                                client.publish_diagnostics(uri, diags, version).await;
                            }
                        }
                        diag_timer = None;
                        // Don't block — fall through so the next iteration can
                        // check the background queue.
                        None
                    }
                    result = rx.recv() => match result {
                        Some(ev) => {
                            // New event arrived — only discard diagnostics for the
                            // affected file, not all files. Clearing everything would
                            // lose diagnostics for unrelated files that completed
                            // analysis during the quiescence window.
                            match &ev {
                                AnalysisEvent::FileChanged { path, .. }
                                | AnalysisEvent::ReanalyzeFile { path } => {
                                    pending_diags.remove(path);
                                }
                                AnalysisEvent::FileClosed { .. }
                                | AnalysisEvent::WarmupComplete { .. } => {}
                            }
                            diag_timer = None;
                            Some(ev)
                        }
                        None => return,
                    }
                }
            } else {
                match rx.recv().await {
                    Some(ev) => Some(ev),
                    None => return,
                }
            };

            // ── Phase 2: Drain all pending events (RA-style coalescing) ──
            //
            // Like RA's `while let Ok(msg) = receiver.try_recv()` pattern after
            // handling the first event. With FULL document sync, only the latest
            // text per file matters.
            let mut changes: HashMap<PathBuf, String> = HashMap::new();
            let mut closed: Vec<PathBuf> = Vec::new();
            let mut warmup_results: Vec<crate::warmup::WarmupFileResult> = Vec::new();

            // Helper closure: process a single AnalysisEvent into the
            // appropriate accumulator.
            let process_event = |event: AnalysisEvent,
                                 changes: &mut HashMap<PathBuf, String>,
                                 closed: &mut Vec<PathBuf>,
                                 warmup_results: &mut Vec<crate::warmup::WarmupFileResult>,
                                 file_versions: &mut HashMap<PathBuf, i32>,
                                 state: &Mutex<AnalysisState>| {
                match event {
                    AnalysisEvent::FileChanged {
                        path,
                        text,
                        version,
                    } => {
                        if let Some(v) = version {
                            file_versions.insert(path.clone(), v);
                        }
                        changes.insert(path, text);
                    }
                    AnalysisEvent::FileClosed { path } => {
                        changes.remove(&path);
                        closed.push(path);
                    }
                    AnalysisEvent::ReanalyzeFile { path } => {
                        let text = {
                            let st = state.lock();
                            st.files
                                .get(&path)
                                .map(|a| a.nix_file.contents(&st.db).to_owned())
                        };
                        if let Some(text) = text {
                            changes.insert(path, text);
                        } else {
                            log::debug!("ReanalyzeFile for {:?}: file not in DB, skipping", path);
                        }
                    }
                    AnalysisEvent::WarmupComplete { results } => {
                        warmup_results.extend(results);
                    }
                }
            };

            // Process the first event (None when the background queue woke us).
            if let Some(first_event) = first_event {
                process_event(
                    first_event,
                    &mut changes,
                    &mut closed,
                    &mut warmup_results,
                    &mut file_versions,
                    &state,
                );
            }

            // Drain remaining (like RA's coalesce loop).
            while let Ok(event) = rx.try_recv() {
                process_event(
                    event,
                    &mut changes,
                    &mut closed,
                    &mut warmup_results,
                    &mut file_versions,
                    &state,
                );
            }

            // Handle closed files: remove from pending diagnostics, versions,
            // and ephemeral stubs.
            for path in &closed {
                pending_diags.remove(path);
                file_versions.remove(path);
                let dependents = state.lock().remove_ephemeral_stub(path);
                // Schedule re-analysis for files that depended on the closed file's type.
                for dep_path in dependents {
                    event_tx
                        .send(AnalysisEvent::ReanalyzeFile { path: dep_path })
                        .ok();
                }
            }

            // ── Warmup result merging ──
            //
            // If the batch warmup completed, merge its results into LSP state.
            // Skip files that the user already opened/edited (they have fresher
            // analysis from the normal event path).
            if !warmup_results.is_empty() {
                log::info!(
                    "merging {} warmup results into LSP state",
                    warmup_results.len()
                );
                let dc = diag_config.lock().clone();

                for result in warmup_results {
                    // Skip if user already opened this file (has a version).
                    if file_versions.contains_key(&result.path) {
                        log::debug!(
                            "warmup: skipping {} (user already opened)",
                            result.path.display()
                        );
                        continue;
                    }

                    // Skip if there's already a snapshot with inference data
                    // (e.g. from demand-driven inference triggered by a user file).
                    if _snapshots
                        .get(&result.path)
                        .is_some_and(|s| s.inference.is_some())
                    {
                        continue;
                    }

                    // Write snapshot to DashMap (handlers can read immediately).
                    _snapshots.insert(result.path.clone(), result.to_snapshot());

                    // Record import deps and store in legacy state.files.
                    {
                        let mut st = state.lock();
                        st.record_import_deps(&result.path, &result.import_paths);
                        // Signature is already in the coordinator (set during warmup).
                        st.files.insert(result.path.clone(), result.file_analysis);
                    }

                    // Buffer diagnostics for quiescence publication.
                    if dc.enable {
                        if let Some(snap) = _snapshots.get(&result.path) {
                            let root = snap.syntax.parsed.tree();
                            let file_uri = Url::from_file_path(&result.path)
                                .unwrap_or_else(|_| Url::parse("file:///unknown").unwrap());
                            let mut diags = crate::diagnostics::to_lsp_diagnostics(
                                &result.diagnostics,
                                &snap.syntax.source_map,
                                &snap.syntax.line_index,
                                &root,
                                &file_uri,
                            );
                            diags.extend(crate::diagnostics::unknown_type_diagnostics(
                                &result.inference_data.check_result,
                                &snap.syntax.module,
                                &snap.syntax.source_map,
                                &snap.syntax.line_index,
                                &root,
                                dc.unknown_type,
                            ));
                            pending_diags.insert(result.path.clone(), diags);
                        }
                    }
                }

                // Start the quiescence timer so diagnostics get published.
                diag_timer = Some(Box::pin(tokio::time::sleep(Duration::from_millis(
                    DIAGNOSTIC_QUIESCENCE_MS,
                ))));

                // If there are no user-driven changes to process, continue to
                // the next loop iteration (publish diagnostics via quiescence).
                if changes.is_empty() {
                    continue;
                }
            }

            // ── Phase 3: Analyze each changed file ──
            //
            // Split into syntax + inference phases. The mutex is held only for
            // the fast syntax phase (~5-50ms). SyntaxData is written to the
            // DashMap immediately, making handlers responsive. Inference runs
            // without the mutex, so handlers never block on type inference.
            //
            // Reset the shared cancel flag for this batch. schedule_analysis()
            // or did_close() may set it to true during inference.
            cancel_flag.store(false, Ordering::Relaxed);

            let mut any_completed = false;

            for (path, text) in &changes {
                // Check for new events or external cancellation between files.
                // If the user typed more (schedule_analysis sets the flag),
                // bail out and let the next loop iteration coalesce them.
                if !rx.is_empty() || cancel_flag.load(Ordering::Relaxed) {
                    break;
                }

                let file_name = path
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_else(|| path.display().to_string());

                // Phase A: Syntax update (mutex held ~5-50ms).
                let (syntax_data, intermediate, syntax_duration) = {
                    let mut st = state.lock();
                    st.update_syntax_phase_a(path.clone(), text.clone())
                };
                // mutex released here

                // Write SyntaxData to DashMap immediately — handlers can read
                // fresh syntax data while inference is still running.
                {
                    // Preserve existing inference data when updating syntax.
                    let prev_inference = _snapshots
                        .get(path)
                        .and_then(|snap| snap.inference.as_ref().cloned());
                    _snapshots.insert(
                        path.clone(),
                        FileSnapshot {
                            syntax: syntax_data,
                            inference: prev_inference,
                        },
                    );
                }

                // Check for cancellation between phases. If a new edit arrived
                // during Phase A, bail out and let the loop re-coalesce.
                if cancel_flag.load(Ordering::Relaxed) {
                    continue;
                }

                // Phase B: Import resolution with demand-driven inference.
                // No state lock needed — uses the coordinator Arc directly.
                // Unopened imported files are inferred from disk on demand.
                let (inference_inputs, import_targets, name_to_import, import_duration) =
                    crate::state::resolve_imports_phase_b(
                        &coordinator,
                        Some(&*lsp_syntax_provider),
                        &intermediate,
                    );

                // Update DashMap with import data from Phase B.
                if let Some(mut snap) = _snapshots.get_mut(path) {
                    snap.syntax.import_targets = import_targets;
                    snap.syntax.name_to_import = name_to_import;
                }

                // Phase C: Type inference (NO mutex held).
                // User-triggered files skip the RSS limit so editing works
                // even when RSS is high. Background files go through warmup.
                let mut inference_inputs = inference_inputs;
                inference_inputs.core.rss_limit_mb = None;
                let (check_result, infer_duration) = crate::state::run_inference(&inference_inputs);

                let was_cancelled = cancel_flag.load(Ordering::Relaxed);
                let total = syntax_duration + import_duration + infer_duration;
                let timing = crate::state::AnalysisTiming {
                    parse: syntax_duration, // folded for now
                    lower: Duration::ZERO,
                    name_res: Duration::ZERO,
                    imports: Duration::ZERO,
                    type_check: infer_duration,
                    total,
                };
                let timing_msg = format!("{file_name}: {timing}");
                if was_cancelled {
                    log::info!("{timing_msg} (cancelled)");
                } else {
                    log::info!("{timing_msg}");
                }

                // Phase C: Store inference results in DashMap and legacy state.
                if let Some(mut snap) = _snapshots.get_mut(path) {
                    snap.inference = Some(InferenceData {
                        check_result: check_result.clone(),
                    });
                }

                // Also store in legacy state.files for backward compat.
                // Extract import paths for dependency tracking.
                let import_paths: Vec<PathBuf> = inference_inputs
                    .import_targets
                    .values()
                    .cloned()
                    .collect::<std::collections::HashSet<_>>()
                    .into_iter()
                    .collect();
                let file_analysis =
                    crate::state::build_file_analysis(inference_inputs, check_result.clone());

                // Extract root type and update ephemeral stub. If the stub
                // changed, schedule re-analysis for all dependents.
                // Build an OwnedTy from the TyRef + the inference arena so the
                // type is self-contained (valid across file boundaries).
                let root_ty: Option<lang_ty::OwnedTy> = file_analysis
                    .check_result
                    .inference
                    .as_ref()
                    .and_then(|inf| {
                        inf.expr_ty_map
                            .get(file_analysis.module.entry_expr)
                            .map(|&ty_ref| {
                                lang_ty::OwnedTy::new(std::sync::Arc::clone(&inf.arena), ty_ref)
                            })
                    });

                let mut reanalyze_paths = Vec::new();
                {
                    let mut st = state.lock();
                    st.files.insert(path.clone(), file_analysis);
                    st.record_import_deps(path, &import_paths);
                    if let Some(owned_ty) = root_ty {
                        if st.update_ephemeral_stub(path, owned_ty) {
                            reanalyze_paths = st.get_dependents(path);
                        }
                    }
                }

                // Queue re-analysis for dependents (outside the lock).
                for dep_path in reanalyze_paths {
                    if dep_path != *path {
                        event_tx
                            .send(AnalysisEvent::ReanalyzeFile { path: dep_path })
                            .ok();
                    }
                }

                let dc = diag_config.lock().clone();
                let diags = if dc.enable && !was_cancelled {
                    if let Some(snap) = _snapshots.get(path) {
                        let root = snap.syntax.parsed.tree();
                        let file_uri = Url::from_file_path(path)
                            .unwrap_or_else(|_| Url::parse("file:///unknown").unwrap());
                        let mut diags = crate::diagnostics::to_lsp_diagnostics(
                            &check_result.diagnostics,
                            &snap.syntax.source_map,
                            &snap.syntax.line_index,
                            &root,
                            &file_uri,
                        );
                        // Append unknown-type diagnostics for `?`-typed bindings.
                        diags.extend(crate::diagnostics::unknown_type_diagnostics(
                            &check_result,
                            &snap.syntax.module,
                            &snap.syntax.source_map,
                            &snap.syntax.line_index,
                            &root,
                            dc.unknown_type,
                        ));
                        diags
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                };

                if was_cancelled {
                    break;
                }

                // Clear pending_text for this file (analysis caught up).
                {
                    let mut pt = pending_text.lock();
                    if pt.get(path).is_some_and(|t| t == text) {
                        pt.remove(path);
                    }
                }

                client.log_message(MessageType::INFO, &timing_msg).await;

                // ── Phase 4: Defer diagnostic publication (quiescence) ──
                pending_diags.insert(path.clone(), diags);
                any_completed = true;
            }

            if any_completed {
                diag_timer = Some(Box::pin(tokio::time::sleep(Duration::from_millis(
                    DIAGNOSTIC_QUIESCENCE_MS,
                ))));
            }
        }
    });
}

#[tower_lsp::async_trait]
impl LanguageServer for TixLanguageServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        if let Some(ref root_uri) = params.root_uri {
            log::info!("Workspace root: {}", root_uri.as_str());
        }

        if let Some(ref info) = params.client_info {
            log::info!(
                "Client: {}{}",
                info.name,
                info.version
                    .as_deref()
                    .map_or(String::new(), |v| format!(" v{v}")),
            );
        }

        // Parse editor-provided settings from initializationOptions.
        if let Some(opts) = params.initialization_options {
            match serde_json::from_value::<TixConfig>(opts) {
                Ok(init_config) => {
                    if !init_config.stubs.is_empty() {
                        log::info!("Editor provided {} stub path(s)", init_config.stubs.len(),);
                        // Rebuild the registry to include both CLI and
                        // editor-configured stubs.
                        let registry = self.build_registry(&init_config);
                        self.state.lock().reload_registry(registry);
                    }
                    *self.config.lock() = init_config;
                }
                Err(e) => {
                    log::warn!("Failed to parse initializationOptions: {e}");
                }
            }
        }

        // Discover tix.toml project config from the workspace root.
        if let Some(root_uri) = params.root_uri {
            if let Some(root_path) = uri_to_path(&root_uri) {
                if let Some(config_path) = crate::project_config::find_config(&root_path) {
                    let config_dir = config_path
                        .parent()
                        .unwrap_or(std::path::Path::new("."))
                        .to_path_buf();

                    match crate::project_config::load_config(&config_path) {
                        Ok(project_cfg) => {
                            log::info!("Loaded project config from {}", config_path.display());

                            if !project_cfg.stubs.is_empty() {
                                log::info!("Project stubs: {}", project_cfg.stubs.join(", "),);
                            }
                            if !project_cfg.context.is_empty() {
                                log::info!(
                                    "Project contexts: {}",
                                    project_cfg
                                        .context
                                        .keys()
                                        .cloned()
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                );
                            }

                            // Load stubs from tix.toml config.
                            let mut state = self.state.lock();
                            for stub in &project_cfg.stubs {
                                let stub_path = config_dir.join(stub);
                                if let Err(e) = crate::load_stubs(
                                    Arc::make_mut(&mut state.registry),
                                    &stub_path,
                                ) {
                                    log::warn!(
                                        "Failed to load config stub '{}': {e}",
                                        stub_path.display()
                                    );
                                }
                            }

                            // Apply diagnostics overrides from tix.toml (project
                            // config is the base; editor settings override later).
                            if let Some(diag_proj) = &project_cfg.diagnostics {
                                let mut dc = self.diag_config.lock();
                                if let Some(level) = diag_proj.unknown_type {
                                    dc.unknown_type = level;
                                }
                            }

                            // Resolve analyze globs before moving config into state.
                            let analyze_files = crate::project_config::resolve_analyze_globs(
                                &project_cfg,
                                &config_dir,
                            );

                            state.project_config = Some(project_cfg.clone());
                            state.config_dir = Some(config_dir.clone());
                            drop(state); // release lock before file I/O

                            // Update the demand-driven syntax provider so it
                            // resolves context_args for files inferred from disk.
                            self.syntax_provider
                                .update_config(Some(project_cfg), Some(config_dir));

                            // Spawn batch warmup for [project] analyze files.
                            // Runs on spawn_blocking so the async analysis loop
                            // stays responsive to user edits during warmup.
                            if !analyze_files.is_empty() {
                                log::info!(
                                    "Spawning batch warmup for {} project files",
                                    analyze_files.len()
                                );
                                let files: Vec<(PathBuf, String)> = analyze_files
                                    .into_iter()
                                    .filter_map(|p| {
                                        std::fs::read_to_string(&p).ok().map(|t| (p, t))
                                    })
                                    .collect();

                                let (
                                    warmup_registry,
                                    warmup_coordinator,
                                    warmup_project_config,
                                    warmup_config_dir,
                                    warmup_rss_limit,
                                ) = {
                                    let st = self.state.lock();
                                    (
                                        Arc::clone(&st.registry),
                                        Arc::clone(&st.coordinator),
                                        st.project_config.clone(),
                                        st.config_dir.clone(),
                                        st.rss_limit_mb,
                                    )
                                };
                                let event_tx = self.event_tx.clone();

                                tokio::task::spawn_blocking(move || {
                                    let results = crate::warmup::run_batch_warmup(
                                        files,
                                        warmup_registry,
                                        &warmup_coordinator,
                                        warmup_project_config.as_ref(),
                                        warmup_config_dir.as_deref(),
                                        warmup_rss_limit,
                                    );
                                    if !results.is_empty() {
                                        event_tx
                                            .send(AnalysisEvent::WarmupComplete { results })
                                            .ok();
                                    }
                                });
                            }
                        }
                        Err(e) => {
                            log::warn!("Failed to load {}: {e}", config_path.display());
                        }
                    }
                } else {
                    log::info!("No tix.toml found");
                }
            }
        }

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    // Full document sync: the editor sends the entire file on each change.
                    // Simpler than incremental; fine for MVP.
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string()]),
                    resolve_provider: Some(true),
                    ..Default::default()
                }),
                document_symbol_provider: Some(OneOf::Left(true)),
                document_link_provider: Some(DocumentLinkOptions {
                    resolve_provider: Some(false),
                    work_done_progress_options: Default::default(),
                }),
                document_formatting_provider: Some(OneOf::Left(true)),
                selection_range_provider: Some(SelectionRangeProviderCapability::Simple(true)),
                references_provider: Some(OneOf::Left(true)),
                document_highlight_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: Default::default(),
                })),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend: crate::semantic_tokens::legend(),
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            range: None,
                            work_done_progress_options: Default::default(),
                        },
                    ),
                ),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                inlay_hint_provider: Some(OneOf::Left(true)),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec![" ".to_string()]),
                    retrigger_characters: None,
                    work_done_progress_options: Default::default(),
                }),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        let msg =
            {
                let state = self.state.lock();
                let config = self.config.lock();
                format!(
                "tix lsp ready — {} type aliases, {} global vals, diagnostics {}, inlay hints {}",
                state.registry.alias_count(),
                state.registry.global_vals().len(),
                if config.diagnostics.enable { "on" } else { "off" },
                if config.inlay_hints.enable { "on" } else { "off" },
            )
            };
        log::info!("{msg}");
        self.client.log_message(MessageType::INFO, msg).await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let version = params.text_document.version;
        self.schedule_analysis(
            params.text_document.uri,
            params.text_document.text,
            Some(version),
        );
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // With FULL sync, there's exactly one content change containing the full text.
        let version = params.text_document.version;
        if let Some(change) = params.content_changes.into_iter().next() {
            self.schedule_analysis(params.text_document.uri, change.text, Some(version));
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        // Clear diagnostics immediately when a file is closed.
        self.client
            .publish_diagnostics(params.text_document.uri.clone(), vec![], None)
            .await;

        if let Some(path) = uri_to_path(&params.text_document.uri) {
            self.cancel_flag.store(true, Ordering::Relaxed);
            self.pending_text.lock().remove(&path);
            self.state.lock().files.remove(&path);
            self.event_tx.send(AnalysisEvent::FileClosed { path }).ok();
        }
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        let new_config = match serde_json::from_value::<TixConfig>(params.settings) {
            Ok(c) => c,
            Err(e) => {
                log::warn!("Failed to parse configuration: {e}");
                return;
            }
        };

        // Check if stubs changed — if so, rebuild the registry and re-analyze.
        let stubs_changed = {
            let old = self.config.lock();
            old.stubs != new_config.stubs
        };

        // Update the shared diagnostics config so the analysis loop picks it up.
        *self.diag_config.lock() = new_config.diagnostics.clone();

        // Collect diagnostics to publish while holding the lock, then
        // release the lock before awaiting the publish calls.
        let file_diagnostics = if stubs_changed {
            let registry = self.build_registry(&new_config);
            let mut state = self.state.lock();
            state.reload_registry(registry);

            let dc = new_config.diagnostics.clone();
            state
                .files
                .iter()
                .filter_map(|(path, analysis)| {
                    let uri = Url::from_file_path(path).ok()?;
                    let diags = if dc.enable {
                        let root = analysis.parsed.tree();
                        let mut diags = crate::diagnostics::to_lsp_diagnostics(
                            &analysis.check_result.diagnostics,
                            &analysis.source_map,
                            &analysis.line_index,
                            &root,
                            &uri,
                        );
                        diags.extend(crate::diagnostics::unknown_type_diagnostics(
                            &analysis.check_result,
                            &analysis.module,
                            &analysis.source_map,
                            &analysis.line_index,
                            &root,
                            dc.unknown_type,
                        ));
                        diags
                    } else {
                        vec![]
                    };
                    Some((uri, diags))
                })
                .collect::<Vec<_>>()
        } else {
            vec![]
        };

        for (uri, diags) in file_diagnostics {
            self.client.publish_diagnostics(uri, diags, None).await;
        }

        *self.config.lock() = new_config;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        // Hover needs docs from the registry — lock state briefly for that.
        let docs = self.state.lock().registry.docs.clone();
        self.with_snapshot(uri, |snapshot, root| {
            crate::hover::hover(snapshot, pos, root, &docs)
        })
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        self.with_snapshot(uri, |snapshot, root| {
            crate::signature_help::signature_help(snapshot, pos, root)
        })
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        // goto_definition needs &AnalysisState for cross-file resolution
        // (loading target files from the Salsa DB). Lock state alongside
        // the DashMap snapshot — no deadlock risk since the analysis loop
        // never holds both simultaneously.
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return Ok(None),
        };
        let snap_ref = match self.snapshots.get(&path) {
            Some(s) => s,
            None => return Err(content_modified_error()),
        };
        let root = snap_ref.syntax.parsed.tree();
        let state = self.state.lock();
        Ok(
            crate::goto_def::goto_definition(&state, &snap_ref, pos, &uri, &root)
                .map(GotoDefinitionResponse::Scalar),
        )
    }

    async fn goto_type_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return Ok(None),
        };
        let snap_ref = match self.snapshots.get(&path) {
            Some(s) => s,
            None => return Err(content_modified_error()),
        };
        let root = snap_ref.syntax.parsed.tree();
        let registry = &self.state.lock().registry;
        let locs = crate::type_def::goto_type_definition(&snap_ref, pos, &root, registry);
        if locs.is_empty() {
            Ok(None)
        } else {
            Ok(Some(GotoDefinitionResponse::Array(locs)))
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;

        let path = match uri_to_path(uri) {
            Some(p) => p,
            None => return Ok(None),
        };

        let snap_ref = match self.snapshots.get(&path) {
            Some(s) => s,
            None => return Err(content_modified_error()),
        };

        // Lock state briefly for docs only.
        let docs = self.state.lock().registry.docs.clone();

        // Use the freshest available tree: pending_text if the analysis loop
        // hasn't caught up yet (e.g. `.` trigger before debounce), otherwise
        // the snapshot's own parsed tree. The unified completion() handles
        // stale source_map via name-text fallbacks internally.
        let fresh_text = self.pending_text.lock().get(&path).cloned();
        if let Some(ref text) = fresh_text {
            let root = rnix::Root::parse(text).tree();
            let line_index = crate::convert::LineIndex::new(text);
            Ok(crate::completion::completion(
                &snap_ref,
                pos,
                &root,
                &docs,
                &line_index,
            ))
        } else {
            let root = snap_ref.syntax.parsed.tree();
            Ok(crate::completion::completion(
                &snap_ref,
                pos,
                &root,
                &docs,
                &snap_ref.syntax.line_index,
            ))
        }
    }

    async fn completion_resolve(&self, mut item: CompletionItem) -> Result<CompletionItem> {
        // Lazily populate documentation from the DocIndex when the client
        // highlights a completion item. The alias name and field path are
        // stored in the item's `data` field during initial completion.
        if item.documentation.is_none() {
            if let Some(ref data) = item.data {
                let alias = data.get("alias").and_then(|v| v.as_str());
                let path = data.get("path").and_then(|v| v.as_array());
                if let (Some(alias), Some(path_arr)) = (alias, path) {
                    let path: Vec<smol_str::SmolStr> = path_arr
                        .iter()
                        .filter_map(|v| v.as_str().map(smol_str::SmolStr::from))
                        .collect();
                    let state = self.state.lock();
                    if let Some(doc) = state.registry.docs.field_doc(alias, &path) {
                        item.documentation =
                            Some(tower_lsp::lsp_types::Documentation::MarkupContent(
                                tower_lsp::lsp_types::MarkupContent {
                                    kind: tower_lsp::lsp_types::MarkupKind::Markdown,
                                    value: doc.to_string(),
                                },
                            ));
                    }
                }
            }
        }
        Ok(item)
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            let symbols = crate::document_symbol::document_symbols(snapshot, root);
            Some(DocumentSymbolResponse::Nested(symbols))
        })
    }

    async fn document_link(&self, params: DocumentLinkParams) -> Result<Option<Vec<DocumentLink>>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            Some(crate::document_link::document_links(snapshot, root))
        })
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            // Get file text from the green tree (Send-safe) instead of the Salsa DB.
            let contents = root.syntax().text().to_string();
            crate::formatting::format_document(&contents, &snapshot.syntax.line_index)
        })
    }

    async fn selection_range(
        &self,
        params: SelectionRangeParams,
    ) -> Result<Option<Vec<SelectionRange>>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            Some(crate::selection_range::selection_ranges(
                snapshot,
                params.positions,
                root,
            ))
        })
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let include_declaration = params.context.include_declaration;
        self.with_snapshot(&uri, |snapshot, root| {
            Some(crate::references::find_references(
                snapshot,
                pos,
                &uri,
                root,
                include_declaration,
            ))
        })
    }

    async fn document_highlight(
        &self,
        params: DocumentHighlightParams,
    ) -> Result<Option<Vec<DocumentHighlight>>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        self.with_snapshot(uri, |snapshot, root| {
            Some(crate::document_highlight::document_highlight(
                snapshot, pos, root,
            ))
        })
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        let uri = &params.text_document.uri;
        let pos = params.position;
        log::debug!("prepare_rename: uri={uri}, pos={pos:?}");
        let result = self.with_snapshot(uri, |snapshot, root| {
            crate::rename::prepare_rename(snapshot, pos, root)
        });
        log::debug!("prepare_rename: result={result:?}");
        result
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let new_name = params.new_name;
        let path = uri_to_path(&uri);

        // Rename needs &AnalysisState for cross-file edits. Lock state
        // alongside the DashMap snapshot.
        let (edit, warning) = {
            let file_path = match &path {
                Some(p) => p,
                None => return Ok(None),
            };
            let snap_ref = match self.snapshots.get(file_path) {
                Some(s) => s,
                None => return Err(content_modified_error()),
            };
            let root = snap_ref.syntax.parsed.tree();
            let state = self.state.lock();
            let result = crate::rename::rename(
                &snap_ref,
                pos,
                &new_name,
                &uri,
                &root,
                Some(&state),
                path.as_ref(),
            );

            match result {
                Some(r) => (Some(r.edit), r.warning),
                None => (None, None),
            }
        };

        // Surface the cross-file rename warning in the editor's output panel.
        if let Some(msg) = warning {
            self.client.show_message(MessageType::WARNING, &msg).await;
        }

        Ok(edit)
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            let tokens = crate::semantic_tokens::semantic_tokens(snapshot, root);
            Some(SemanticTokensResult::Tokens(SemanticTokens {
                result_id: None,
                data: tokens,
            }))
        })
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        if !self.config.lock().inlay_hints.enable {
            return Ok(Some(vec![]));
        }
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            Some(crate::inlay_hint::inlay_hints(snapshot, params.range, root))
        })
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        self.with_snapshot(&params.text_document.uri, |snapshot, root| {
            let actions = crate::code_actions::code_actions(snapshot, &params, root);
            if actions.is_empty() {
                None
            } else {
                Some(actions)
            }
        })
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let state = self.state.lock();
        Ok(crate::workspace_symbols::handle_workspace_symbols(
            &state,
            &params.query,
        ))
    }
}

/// LSP error indicating the document has been modified and the request should
/// be retried. Editors like VS Code and Neovim handle this gracefully by
/// automatically retrying after a short delay.
fn content_modified_error() -> tower_lsp::jsonrpc::Error {
    tower_lsp::jsonrpc::Error {
        code: tower_lsp::jsonrpc::ErrorCode::ContentModified,
        message: "content modified".into(),
        data: None,
    }
}

/// Convert a file:// URI to a PathBuf, canonicalizing to resolve symlinks and
/// `..` components. This ensures all downstream caches (snapshots, pending_text,
/// state.files, Salsa DB) use consistent keys. Falls back to the raw path for
/// files that don't exist on disk yet (e.g. unsaved buffers).
fn uri_to_path(uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
        return None;
    }
    uri.to_file_path()
        .ok()
        .map(|p| p.canonicalize().unwrap_or(p))
}
