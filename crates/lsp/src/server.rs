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
// analyzed, the in-flight analysis is cancelled via an Arc<AtomicBool> flag
// that's checked periodically by the inference engine (alongside the existing
// deadline mechanism). This avoids blocking the editor while waiting for a
// 10-second timeout on a stale version of the file.

use std::collections::HashMap;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use parking_lot::Mutex;
use tokio::sync::mpsc;

use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::config::TixConfig;
use crate::state::{AnalysisState, FileAnalysis};

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
    FileChanged { path: PathBuf, text: String },
    /// File closed (didClose). Clears pending diagnostics for this file.
    FileClosed { path: PathBuf },
}

pub struct TixLanguageServer {
    client: Client,
    state: Arc<Mutex<AnalysisState>>,
    config: Mutex<TixConfig>,
    /// CLI-provided stub paths, kept so they can be re-loaded when
    /// the config changes at runtime.
    cli_stub_paths: Vec<PathBuf>,
    /// When true, skip loading built-in nixpkgs stubs.
    no_default_stubs: bool,
    /// Channel to the single analysis loop (like RA's VFS channel).
    event_tx: mpsc::UnboundedSender<AnalysisEvent>,
    /// Cancel flag for the currently running analysis. schedule_analysis()
    /// sets this to true; the analysis loop swaps in a fresh flag before
    /// starting each batch.
    current_cancel: Arc<Mutex<Arc<AtomicBool>>>,
    /// Latest document text received via didChange/didOpen, stored immediately
    /// so completion can re-parse on the fly while analysis catches up.
    /// Cleared once analysis catches up.
    pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
}

impl TixLanguageServer {
    pub fn new(
        client: Client,
        registry: TypeAliasRegistry,
        cli_stub_paths: Vec<PathBuf>,
        no_default_stubs: bool,
    ) -> Self {
        let (event_tx, event_rx) = mpsc::unbounded_channel();
        let state = Arc::new(Mutex::new(AnalysisState::new(registry)));
        let pending_text = Arc::new(Mutex::new(HashMap::new()));
        let current_cancel = Arc::new(Mutex::new(Arc::new(AtomicBool::new(false))));

        // Spawn the analysis loop eagerly. diagnostics_enabled defaults to
        // true; if the editor sends a different config via initializationOptions
        // before opening files, it takes effect before any analysis runs.
        spawn_analysis_loop(
            event_rx,
            state.clone(),
            client.clone(),
            pending_text.clone(),
            current_cancel.clone(),
            true, // diagnostics default on
        );

        Self {
            client,
            state,
            config: Mutex::new(TixConfig::default()),
            cli_stub_paths,
            no_default_stubs,
            event_tx,
            current_cancel,
            pending_text,
        }
    }

    /// Schedule analysis for a file. The text is stored immediately in
    /// `pending_text` so that request handlers (e.g. completion) can re-parse
    /// it on the fly, then an event is sent to the analysis loop which will
    /// coalesce it with any other pending edits.
    fn schedule_analysis(&self, uri: Url, text: String) {
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return,
        };

        // Store latest text immediately (completion can use it right away).
        self.pending_text.lock().insert(path.clone(), text.clone());

        // Cancel any in-flight analysis (like RA's trigger_cancellation()).
        self.current_cancel.lock().store(true, Ordering::Relaxed);

        // Send to analysis loop — it will drain and coalesce.
        self.event_tx
            .send(AnalysisEvent::FileChanged { path, text })
            .ok();
    }

    /// Lock the state, look up the file analysis for `uri`, and call `f`.
    ///
    /// Returns `ContentModified` if the file hasn't been analyzed yet — this
    /// tells the editor "data isn't ready, retry shortly" rather than "there
    /// are no results." Returns `Ok(None)` only for non-file URIs.
    fn with_analysis<T>(
        &self,
        uri: &Url,
        f: impl FnOnce(&AnalysisState, &FileAnalysis) -> Option<T>,
    ) -> Result<Option<T>> {
        let path = match uri_to_path(uri) {
            Some(p) => p,
            None => return Ok(None),
        };
        let state = self.state.lock();
        let analysis = match state.get_file(&path) {
            Some(a) => a,
            None => return Err(content_modified_error()),
        };
        Ok(f(&state, analysis))
    }

    /// Build a fresh TypeAliasRegistry from CLI stubs and config stubs.
    fn build_registry(&self, config: &TixConfig) -> TypeAliasRegistry {
        let mut registry = if self.no_default_stubs {
            TypeAliasRegistry::new()
        } else {
            TypeAliasRegistry::with_builtins()
        };

        // Allow overriding built-in context stubs via env var.
        if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
            log::info!("TIX_BUILTIN_STUBS override: {dir}");
            registry.set_builtin_stubs_dir(std::path::PathBuf::from(dir));
        }

        // CLI stubs are always loaded first.
        for stub_path in &self.cli_stub_paths {
            if let Err(e) = crate::load_stubs(&mut registry, stub_path) {
                log::warn!("Failed to load CLI stubs from {}: {e}", stub_path.display());
            }
        }

        // Then config-provided stubs.
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
    state: Arc<Mutex<AnalysisState>>,
    client: Client,
    pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
    current_cancel: Arc<Mutex<Arc<AtomicBool>>>,
    diagnostics_enabled: bool,
) {
    tokio::spawn(async move {
        // Pending diagnostics waiting for quiescence, keyed by path.
        let mut pending_diags: HashMap<PathBuf, Vec<Diagnostic>> = HashMap::new();
        let mut diag_timer: Option<Pin<Box<tokio::time::Sleep>>> = None;

        loop {
            // ── Phase 1: Wait for event or diagnostic timer ──
            //
            // Like RA's select! in next_event(): block until something happens.
            // If we have pending diagnostics, race the quiescence timer against
            // new events. New events reset the timer (like RA discards stale
            // diagnostics when state changes).
            let first_event = if let Some(ref mut timer) = diag_timer {
                tokio::select! {
                    _ = &mut *timer => {
                        // Quiescence reached — publish all pending diagnostics.
                        for (path, diags) in pending_diags.drain() {
                            if let Ok(uri) = Url::from_file_path(&path) {
                                client.publish_diagnostics(uri, diags, None).await;
                            }
                        }
                        diag_timer = None;
                        // Now block until next event.
                        match rx.recv().await {
                            Some(ev) => ev,
                            None => return,
                        }
                    }
                    result = rx.recv() => match result {
                        Some(ev) => {
                            // New event arrived — stale diagnostics discarded,
                            // timer reset after next analysis completes.
                            pending_diags.clear();
                            diag_timer = None;
                            ev
                        }
                        None => return,
                    }
                }
            } else {
                match rx.recv().await {
                    Some(ev) => ev,
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

            // Process the first event.
            match first_event {
                AnalysisEvent::FileChanged { path, text } => {
                    changes.insert(path, text);
                }
                AnalysisEvent::FileClosed { path } => {
                    closed.push(path);
                }
            }

            // Drain remaining (like RA's coalesce loop).
            while let Ok(event) = rx.try_recv() {
                match event {
                    AnalysisEvent::FileChanged { path, text } => {
                        changes.insert(path, text);
                    }
                    AnalysisEvent::FileClosed { path } => {
                        changes.remove(&path);
                        closed.push(path);
                    }
                }
            }

            // Handle closed files: remove from pending diagnostics.
            for path in &closed {
                pending_diags.remove(path);
            }

            if changes.is_empty() {
                continue;
            }

            // ── Phase 3: Analyze each changed file ──
            //
            // Like RA's process_changes() → apply_change(), but we do
            // per-file analysis since tix doesn't batch via Salsa.
            // Create a fresh cancel flag (like RA's trigger_cancellation()).
            let cancel_flag = Arc::new(AtomicBool::new(false));
            *current_cancel.lock() = cancel_flag.clone();

            let mut any_completed = false;

            for (path, text) in &changes {
                // Check for new events between files. If the user typed more,
                // bail out and let the next loop iteration coalesce them.
                // This mirrors RA's cancellation-on-new-revision pattern.
                if !rx.is_empty() {
                    cancel_flag.store(true, Ordering::Relaxed);
                    break;
                }

                let file_name = path
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_else(|| path.display().to_string());

                let (diags, timing_msg, was_cancelled) = {
                    let mut st = state.lock();
                    let (analysis, timing) = st.update_file_with_cancel(
                        path.clone(),
                        text.clone(),
                        cancel_flag.clone(),
                    );

                    let was_cancelled = cancel_flag.load(Ordering::Relaxed);
                    let timing_msg = format!("{file_name}: {timing}");
                    if was_cancelled {
                        log::info!("{timing_msg} (cancelled)");
                    } else {
                        log::info!("{timing_msg}");
                    }

                    let diags = if diagnostics_enabled && !was_cancelled {
                        let root = analysis.parsed.tree();
                        let file_uri = Url::from_file_path(path)
                            .unwrap_or_else(|_| Url::parse("file:///unknown").unwrap());
                        crate::diagnostics::to_lsp_diagnostics(
                            &analysis.check_result.diagnostics,
                            &analysis.source_map,
                            &analysis.line_index,
                            &root,
                            &file_uri,
                        )
                    } else {
                        vec![]
                    };

                    (diags, timing_msg, was_cancelled)
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
                //
                // Like RA's `is_quiescent()` gate. Store diagnostics but
                // don't publish yet. The timer at the top of the loop will
                // publish them if no new edits arrive.
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
                                if let Err(e) = crate::load_stubs(&mut state.registry, &stub_path) {
                                    log::warn!(
                                        "Failed to load config stub '{}': {e}",
                                        stub_path.display()
                                    );
                                }
                            }

                            if let Some(secs) = project_cfg.deadline {
                                log::info!("Inference deadline: {secs}s (from tix.toml)");
                                state.deadline_secs = secs;
                            }
                            if let Some(secs) = project_cfg.import_deadline {
                                log::info!("Import deadline: {secs}s (from tix.toml)");
                                state.import_deadline_secs = Some(secs);
                            }

                            state.project_config = Some(project_cfg);
                            state.config_dir = Some(config_dir);
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
                "tix-lsp ready — {} type aliases, {} global vals, diagnostics {}, inlay hints {}",
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
        self.schedule_analysis(params.text_document.uri, params.text_document.text);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // With FULL sync, there's exactly one content change containing the full text.
        if let Some(change) = params.content_changes.into_iter().next() {
            self.schedule_analysis(params.text_document.uri, change.text);
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        // Clear diagnostics immediately when a file is closed.
        self.client
            .publish_diagnostics(params.text_document.uri.clone(), vec![], None)
            .await;

        if let Some(path) = uri_to_path(&params.text_document.uri) {
            self.current_cancel.lock().store(true, Ordering::Relaxed);
            self.pending_text.lock().remove(&path);
            self.state.lock().files.remove(&path);
            self.event_tx
                .send(AnalysisEvent::FileClosed { path })
                .ok();
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

        // Collect diagnostics to publish while holding the lock, then
        // release the lock before awaiting the publish calls.
        let file_diagnostics = if stubs_changed {
            let registry = self.build_registry(&new_config);
            let mut state = self.state.lock();
            state.reload_registry(registry);

            let diagnostics_enabled = new_config.diagnostics.enable;
            state
                .files
                .iter()
                .filter_map(|(path, analysis)| {
                    let uri = Url::from_file_path(path).ok()?;
                    let diags = if diagnostics_enabled {
                        let root = analysis.parsed.tree();
                        crate::diagnostics::to_lsp_diagnostics(
                            &analysis.check_result.diagnostics,
                            &analysis.source_map,
                            &analysis.line_index,
                            &root,
                            &uri,
                        )
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
        self.with_analysis(uri, |state, analysis| {
            let root = analysis.parsed.tree();
            crate::hover::hover(analysis, pos, &root, &state.registry.docs)
        })
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        self.with_analysis(uri, |_, analysis| {
            let root = analysis.parsed.tree();
            crate::signature_help::signature_help(analysis, pos, &root)
        })
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        self.with_analysis(&uri, |state, analysis| {
            let root = analysis.parsed.tree();
            crate::goto_def::goto_definition(state, analysis, pos, &uri, &root)
                .map(GotoDefinitionResponse::Scalar)
        })
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;

        let path = match uri_to_path(uri) {
            Some(p) => p,
            None => return Ok(None),
        };

        // Check if we have fresher text than the last completed analysis.
        // This happens when `.` triggers completion before the debounce timer
        // fires — the stale analysis doesn't contain the `.` token.
        let fresh_text = self.pending_text.lock().get(&path).cloned();

        // Use try_lock() so completion never blocks waiting for an in-flight
        // analysis to finish. If the lock is held (inference running), return
        // ContentModified to tell the editor to retry shortly.
        let state = match self.state.try_lock() {
            Some(guard) => guard,
            None => return Err(content_modified_error()),
        };

        let analysis = match state.get_file(&path) {
            Some(a) => a,
            None => return Err(content_modified_error()),
        };

        if let Some(ref text) = fresh_text {
            // Analysis hasn't caught up to the latest edit. Try full
            // completion first — it works when the edit is in-place (e.g.
            // `lib` → `lib.` without shifting ranges). Fall back to
            // syntax-only completion (which handles range-shifted cases
            // via name-text lookup) only if full completion returns None.
            let root = rnix::Root::parse(text).tree();
            let line_index = crate::convert::LineIndex::new(text);
            let full_result = crate::completion::completion(
                analysis,
                pos,
                &root,
                &state.registry.docs,
                &line_index,
            );
            if full_result.is_some() {
                return Ok(full_result);
            }
            Ok(crate::completion::syntax_only_completion(
                analysis,
                pos,
                &root,
                &line_index,
            ))
        } else {
            let root = analysis.parsed.tree();
            Ok(crate::completion::completion(
                analysis,
                pos,
                &root,
                &state.registry.docs,
                &analysis.line_index,
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
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            let symbols = crate::document_symbol::document_symbols(analysis, &root);
            Some(DocumentSymbolResponse::Nested(symbols))
        })
    }

    async fn document_link(&self, params: DocumentLinkParams) -> Result<Option<Vec<DocumentLink>>> {
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            Some(crate::document_link::document_links(analysis, &root))
        })
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        self.with_analysis(&params.text_document.uri, |state, analysis| {
            let contents = analysis.nix_file.contents(&state.db);
            crate::formatting::format_document(contents, &analysis.line_index)
        })
    }

    async fn selection_range(
        &self,
        params: SelectionRangeParams,
    ) -> Result<Option<Vec<SelectionRange>>> {
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            Some(crate::selection_range::selection_ranges(
                analysis,
                params.positions,
                &root,
            ))
        })
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let include_declaration = params.context.include_declaration;
        self.with_analysis(&uri, |_, analysis| {
            let root = analysis.parsed.tree();
            Some(crate::references::find_references(
                analysis,
                pos,
                &uri,
                &root,
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
        self.with_analysis(uri, |_, analysis| {
            let root = analysis.parsed.tree();
            Some(crate::document_highlight::document_highlight(
                analysis, pos, &root,
            ))
        })
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            crate::rename::prepare_rename(analysis, params.position, &root)
        })
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let new_name = params.new_name;
        let path = uri_to_path(&uri);

        let (edit, warning) = {
            let result = self.with_analysis(&uri, |state, analysis| {
                let root = analysis.parsed.tree();
                crate::rename::rename(
                    analysis,
                    pos,
                    &new_name,
                    &uri,
                    &root,
                    Some(state),
                    path.as_ref(),
                )
            })?;

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
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            let tokens = crate::semantic_tokens::semantic_tokens(analysis, &root);
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
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            Some(crate::inlay_hint::inlay_hints(
                analysis,
                params.range,
                &root,
            ))
        })
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        self.with_analysis(&params.text_document.uri, |_, analysis| {
            let root = analysis.parsed.tree();
            let actions = crate::code_actions::code_actions(analysis, &params, &root);
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

/// Convert a file:// URI to a PathBuf. Returns None for non-file URIs.
fn uri_to_path(uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
        return None;
    }
    uri.to_file_path().ok()
}
