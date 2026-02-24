// ==============================================================================
// tower-lsp LanguageServer implementation
// ==============================================================================
//
// Lifecycle (initialize/shutdown) and request dispatch. Analysis runs inside
// spawn_blocking because rnix::Root is !Send + !Sync. The AnalysisState is
// behind a parking_lot::Mutex and all access happens within the blocking task.
//
// Debouncing: didChange/didOpen notifications are debounced per-file (300ms
// default). Rapid edits restart the timer so analysis only runs after the user
// pauses typing.
//
// Cancellation: when a new edit arrives for a file that's currently being
// analyzed, the in-flight analysis is cancelled via an Arc<AtomicBool> flag
// that's checked periodically by the inference engine (alongside the existing
// deadline mechanism). This avoids blocking the editor while waiting for a
// 10-second timeout on a stale version of the file.

use std::collections::HashMap;
use std::path::PathBuf;
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

/// Default debounce delay for `didChange` notifications. `didOpen` uses a
/// shorter delay (see `DEBOUNCE_DELAY_DID_OPEN`) because the user expects
/// immediate feedback when first opening a file.
const DEBOUNCE_DELAY_MS: u64 = 300;

/// Debounce delay for `didOpen` — shorter than `didChange` because the user
/// just opened the file and expects to see types quickly. Still non-zero to
/// coalesce rapid multi-file opens (e.g. editor restoring a session).
const DEBOUNCE_DELAY_DID_OPEN_MS: u64 = 50;

/// Per-file debounce/cancellation state. Each open file gets a background
/// tokio task that receives edit notifications, debounces them, and then
/// runs analysis with a cancellation flag.
struct DebounceWorker {
    /// Send new file contents (and debounce delay) to the background worker.
    tx: mpsc::UnboundedSender<(String, Duration)>,
    /// Cancellation flag for the currently running analysis (if any).
    /// Set to `true` when a newer edit supersedes the in-flight analysis.
    cancel_flag: Arc<AtomicBool>,
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
    /// Per-file debounce workers. Keyed by canonical file path.
    debounce_workers: Mutex<HashMap<PathBuf, DebounceWorker>>,
    /// Latest document text received via didChange/didOpen, stored immediately
    /// before debouncing. Completion handlers check this to get a fresh parse
    /// tree when the debounced analysis hasn't completed yet. Cleared once
    /// analysis catches up.
    pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
}

impl TixLanguageServer {
    pub fn new(
        client: Client,
        registry: TypeAliasRegistry,
        cli_stub_paths: Vec<PathBuf>,
        no_default_stubs: bool,
    ) -> Self {
        Self {
            client,
            state: Arc::new(Mutex::new(AnalysisState::new(registry))),
            config: Mutex::new(TixConfig::default()),
            cli_stub_paths,
            no_default_stubs,
            debounce_workers: Mutex::new(HashMap::new()),
            pending_text: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Schedule analysis for a file. The actual analysis is debounced: rapid
    /// calls within the debounce window only trigger a single analysis run
    /// using the latest content.
    ///
    /// The text is stored immediately in `pending_text` so that request
    /// handlers (e.g. completion) can re-parse it on the fly while the
    /// debounce timer is still running.
    fn schedule_analysis(&self, uri: Url, text: String, debounce_delay: Duration) {
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return,
        };

        // Store the latest text immediately so completion can use it.
        self.pending_text
            .lock()
            .insert(path.clone(), text.clone());

        let mut workers = self.debounce_workers.lock();

        // Check if an existing debounce worker can accept this edit.
        let reuse_existing = if let Some(worker) = workers.get(&path) {
            // Signal cancellation of any in-flight analysis for this file.
            worker.cancel_flag.store(true, Ordering::Relaxed);
            // Check if the worker channel is still open.
            !worker.tx.is_closed()
        } else {
            false
        };

        if reuse_existing {
            workers
                .get(&path)
                .unwrap()
                .tx
                .send((text, debounce_delay))
                .ok();
            return;
        }

        // Create a new debounce worker for this file.
        let (tx, rx) = mpsc::unbounded_channel();
        let cancel_flag = Arc::new(AtomicBool::new(false));

        tx.send((text, debounce_delay)).ok();

        let worker = DebounceWorker {
            tx,
            cancel_flag: cancel_flag.clone(),
        };
        workers.insert(path.clone(), worker);
        drop(workers);

        // Spawn the debounce worker task.
        let client = self.client.clone();
        let state = self.state.clone();
        let diagnostics_enabled = self.config.lock().diagnostics.enable;

        let pending_text = self.pending_text.clone();
        self.spawn_debounce_worker(
            path,
            rx,
            cancel_flag,
            client,
            state,
            diagnostics_enabled,
            pending_text,
        );
    }

    /// Spawn a background task that debounces edits for a single file and
    /// runs analysis after the debounce delay.
    fn spawn_debounce_worker(
        &self,
        path: PathBuf,
        mut rx: mpsc::UnboundedReceiver<(String, Duration)>,
        initial_cancel_flag: Arc<AtomicBool>,
        client: Client,
        state: Arc<Mutex<AnalysisState>>,
        diagnostics_enabled: bool,
        pending_text: Arc<Mutex<HashMap<PathBuf, String>>>,
    ) {
        tokio::spawn(async move {
            // The cancel flag for the current analysis run. Updated each time
            // we start a new analysis.
            let mut current_cancel = initial_cancel_flag;

            while let Some((mut text, mut delay)) = rx.recv().await {
                // Debounce loop: keep consuming new edits until the channel is
                // quiet for the debounce delay.
                loop {
                    tokio::select! {
                        // Wait for the debounce delay to expire.
                        () = tokio::time::sleep(delay) => {
                            break;
                        }
                        // A newer edit arrived — restart the timer.
                        newer = rx.recv() => {
                            match newer {
                                Some((new_text, new_delay)) => {
                                    text = new_text;
                                    delay = new_delay;
                                    // Continue the debounce loop with the new text.
                                }
                                None => {
                                    // Channel closed (file was closed or server
                                    // shutting down). Exit the worker.
                                    return;
                                }
                            }
                        }
                    }
                }

                // Cancel any previous in-flight analysis for this file.
                current_cancel.store(true, Ordering::Relaxed);

                // Create a fresh cancel flag for this analysis run.
                let cancel_flag = Arc::new(AtomicBool::new(false));
                current_cancel = cancel_flag.clone();

                let file_name = path
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_else(|| path.display().to_string());

                // Run analysis. This acquires the AnalysisState lock, which
                // serializes analysis across all files. The cancel flag allows
                // the analysis to be aborted early if a newer edit arrives.
                let (diagnostics, timing_msg, was_cancelled) = {
                    let mut st = state.lock();
                    let (analysis, timing) =
                        st.update_file_with_cancel(path.clone(), text.clone(), cancel_flag.clone());

                    let was_cancelled = cancel_flag.load(Ordering::Relaxed);
                    let timing_msg = format!("{file_name}: {timing}");
                    if was_cancelled {
                        log::info!("{timing_msg} (cancelled)");
                    } else {
                        log::info!("{timing_msg}");
                    }

                    let diags = if diagnostics_enabled && !was_cancelled {
                        let root = analysis.parsed.tree();
                        crate::diagnostics::to_lsp_diagnostics(
                            &analysis.check_result.diagnostics,
                            &analysis.source_map,
                            &analysis.line_index,
                            &root,
                        )
                    } else {
                        vec![]
                    };

                    (diags, timing_msg, was_cancelled)
                };

                // Don't publish results from cancelled analysis — a newer
                // version is already queued.
                if was_cancelled {
                    continue;
                }

                // Analysis completed successfully — clear pending_text, but
                // only if the text hasn't been superseded by an even newer edit.
                {
                    let mut pt = pending_text.lock();
                    if pt.get(&path).map_or(false, |t| *t == text) {
                        pt.remove(&path);
                    }
                }

                // Send timing to the editor's output panel.
                client.log_message(MessageType::INFO, &timing_msg).await;

                let uri = match Url::from_file_path(&path) {
                    Ok(u) => u,
                    Err(_) => continue,
                };
                client.publish_diagnostics(uri, diagnostics, None).await;
            }
        });
    }

    /// Lock the state, look up the file analysis for `uri`, and call `f`.
    /// Returns `Ok(None)` if the URI isn't a file path or the file hasn't been
    /// analyzed yet.
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
            None => return Ok(None),
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
        // Use a short debounce for didOpen — the user expects quick feedback
        // when opening a file, but we still coalesce rapid multi-file opens
        // (e.g. editor restoring a session with many tabs).
        self.schedule_analysis(
            params.text_document.uri,
            params.text_document.text,
            Duration::from_millis(DEBOUNCE_DELAY_DID_OPEN_MS),
        );
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // With FULL sync, there's exactly one content change containing the full text.
        if let Some(change) = params.content_changes.into_iter().next() {
            self.schedule_analysis(
                params.text_document.uri,
                change.text,
                Duration::from_millis(DEBOUNCE_DELAY_MS),
            );
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        // Clear diagnostics when a file is closed.
        self.client
            .publish_diagnostics(params.text_document.uri.clone(), vec![], None)
            .await;

        // Remove the debounce worker and cached analysis.
        if let Some(path) = uri_to_path(&params.text_document.uri) {
            // Cancel any in-flight analysis and remove the worker.
            {
                let mut workers = self.debounce_workers.lock();
                if let Some(worker) = workers.remove(&path) {
                    worker.cancel_flag.store(true, Ordering::Relaxed);
                    // Dropping the sender closes the channel, which will cause
                    // the worker task to exit.
                }
            }

            self.pending_text.lock().remove(&path);

            let mut state = self.state.lock();
            state.files.remove(&path);
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

        // Check if we have fresher text than the last completed analysis.
        // This happens when `.` triggers completion before the debounce timer
        // fires — the stale analysis doesn't contain the `.` token, so we
        // re-parse the latest text to get a fresh syntax tree and LineIndex.
        let fresh_text = uri_to_path(uri).and_then(|p| self.pending_text.lock().get(&p).cloned());

        self.with_analysis(uri, |state, analysis| {
            if let Some(ref text) = fresh_text {
                let root = rnix::Root::parse(text).tree();
                let line_index = crate::convert::LineIndex::new(text);
                crate::completion::completion(
                    analysis,
                    pos,
                    &root,
                    &state.registry.docs,
                    &line_index,
                )
            } else {
                let root = analysis.parsed.tree();
                crate::completion::completion(
                    analysis,
                    pos,
                    &root,
                    &state.registry.docs,
                    &analysis.line_index,
                )
            }
        })
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

/// Convert a file:// URI to a PathBuf. Returns None for non-file URIs.
fn uri_to_path(uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
        return None;
    }
    uri.to_file_path().ok()
}
