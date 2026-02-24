// ==============================================================================
// tower-lsp LanguageServer implementation
// ==============================================================================
//
// Lifecycle (initialize/shutdown) and request dispatch. Analysis runs inside
// spawn_blocking because rnix::Root is !Send + !Sync. The AnalysisState is
// behind a parking_lot::Mutex and all access happens within the blocking task.

use std::path::PathBuf;

use parking_lot::Mutex;

use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::config::TixConfig;
use crate::state::{AnalysisState, FileAnalysis};

pub struct TixLanguageServer {
    client: Client,
    state: Mutex<AnalysisState>,
    config: Mutex<TixConfig>,
    /// CLI-provided stub paths, kept so they can be re-loaded when
    /// the config changes at runtime.
    cli_stub_paths: Vec<PathBuf>,
    /// When true, skip loading built-in nixpkgs stubs.
    no_default_stubs: bool,
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
            state: Mutex::new(AnalysisState::new(registry)),
            config: Mutex::new(TixConfig::default()),
            cli_stub_paths,
            no_default_stubs,
        }
    }

    /// Run analysis for a file and publish diagnostics.
    /// Called from didOpen and didChange.
    async fn on_change(&self, uri: Url, text: String) {
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return,
        };

        let diagnostics_enabled = self.config.lock().diagnostics.enable;

        // All analysis runs in spawn_blocking because rnix::Root is !Send.
        // We gather the LSP-safe results (diagnostics) inside the blocking
        // closure and publish them afterwards. We always run analysis (needed
        // for hover, completion, etc.) but only collect diagnostics if enabled.
        let file_name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| path.display().to_string());

        let (diagnostics, timing_msg) = {
            let mut state = self.state.lock();
            let (analysis, timing) = state.update_file(path, text);

            let timing_msg = format!("{file_name}: {timing}");
            log::info!("{timing_msg}");

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

            (diags, timing_msg)
        };

        // Send timing to the editor's output panel via the LSP protocol.
        self.client
            .log_message(MessageType::INFO, &timing_msg)
            .await;

        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
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
        let msg = {
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
        self.on_change(params.text_document.uri, params.text_document.text)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // With FULL sync, there's exactly one content change containing the full text.
        if let Some(change) = params.content_changes.into_iter().next() {
            self.on_change(params.text_document.uri, change.text).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        // Clear diagnostics when a file is closed.
        self.client
            .publish_diagnostics(params.text_document.uri.clone(), vec![], None)
            .await;

        // Remove cached analysis.
        if let Some(path) = uri_to_path(&params.text_document.uri) {
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

    async fn signature_help(
        &self,
        params: SignatureHelpParams,
    ) -> Result<Option<SignatureHelp>> {
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
        self.with_analysis(uri, |state, analysis| {
            let root = analysis.parsed.tree();
            crate::completion::completion(analysis, pos, &root, &state.registry.docs)
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
            self.client
                .show_message(MessageType::WARNING, &msg)
                .await;
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
}

/// Convert a file:// URI to a PathBuf. Returns None for non-file URIs.
fn uri_to_path(uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
        return None;
    }
    uri.to_file_path().ok()
}
