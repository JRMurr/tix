// ==============================================================================
// tower-lsp LanguageServer implementation
// ==============================================================================
//
// Lifecycle (initialize/shutdown) and request dispatch. Analysis runs inside
// spawn_blocking because rnix::Root is !Send + !Sync. The AnalysisState is
// behind a std::sync::Mutex and all access happens within the blocking task.

use std::path::PathBuf;
use std::sync::Mutex;

use lang_check::aliases::TypeAliasRegistry;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::state::AnalysisState;

pub struct TixLanguageServer {
    client: Client,
    state: Mutex<AnalysisState>,
}

impl TixLanguageServer {
    pub fn new(client: Client, registry: TypeAliasRegistry) -> Self {
        Self {
            client,
            state: Mutex::new(AnalysisState::new(registry)),
        }
    }

    /// Run analysis for a file and publish diagnostics.
    /// Called from didOpen and didChange.
    async fn on_change(&self, uri: Url, text: String) {
        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return,
        };

        // All analysis runs in spawn_blocking because rnix::Root is !Send.
        // We gather the LSP-safe results (diagnostics) inside the blocking
        // closure and publish them afterwards.
        let diagnostics = {
            let mut state = self.state.lock().unwrap();
            let analysis = state.update_file(path, text.clone());

            // Parse again for diagnostic source mapping. The Salsa-cached parse
            // isn't stored (Root is !Send), so we re-parse here. This is cheap
            // for single files.
            let root = rnix::Root::parse(&text).tree();

            let mut diags = crate::diagnostics::to_diagnostics(
                &analysis.check_result.errors,
                &analysis.source_map,
                &analysis.line_index,
                &root,
            );
            diags.extend(crate::diagnostics::warnings_to_diagnostics(
                &analysis.check_result.warnings,
                &analysis.source_map,
                &analysis.line_index,
                &root,
            ));
            diags
        };

        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for TixLanguageServer {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    // Full document sync: the editor sends the entire file on each change.
                    // Simpler than incremental; fine for MVP.
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        log::info!("tix-lsp initialized");
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
            let mut state = self.state.lock().unwrap();
            state.files.remove(&path);
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return Ok(None),
        };

        let state = self.state.lock().unwrap();
        let analysis = match state.get_file(&path) {
            Some(a) => a,
            None => return Ok(None),
        };

        // Re-parse to get a Root we can use for node lookup.
        let contents = analysis.nix_file.contents(&state.db);
        let root = rnix::Root::parse(contents).tree();

        Ok(crate::hover::hover(analysis, pos, &root))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        let path = match uri_to_path(&uri) {
            Some(p) => p,
            None => return Ok(None),
        };

        let state = self.state.lock().unwrap();
        let analysis = match state.get_file(&path) {
            Some(a) => a,
            None => return Ok(None),
        };

        let contents = analysis.nix_file.contents(&state.db);
        let root = rnix::Root::parse(contents).tree();

        let location = crate::goto_def::goto_definition(&state, analysis, pos, &uri, &root);
        Ok(location.map(GotoDefinitionResponse::Scalar))
    }
}

/// Convert a file:// URI to a PathBuf. Returns None for non-file URIs.
fn uri_to_path(uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
        return None;
    }
    uri.to_file_path().ok()
}
