// ==============================================================================
// E2E LSP Test Harness
// ==============================================================================
//
// Exercises the full tower-lsp `Service` pipeline in-process: real
// `LanguageServer` trait impl, real analysis loop with coalescing/cancellation,
// real `DashMap` snapshots, and real quiescence timer — without any
// transport/framing overhead.
//
// `LspService::new()` returns `(LspService<S>, ClientSocket)`:
// - `LspService` implements `tower::Service<Request>` — we send JSON-RPC
//   requests to it directly.
// - `ClientSocket` implements `Stream<Item = Request>` — server-to-client
//   notifications (like `publishDiagnostics`) appear here.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::time::Duration;

use futures::StreamExt;
use lang_check::aliases::TypeAliasRegistry;
use serde_json::json;
use tokio::sync::mpsc;
use tower::{Service, ServiceExt};
use tower_lsp::jsonrpc::{Request, Response};
use tower_lsp::lsp_types::*;
use tower_lsp::LspService;

use std::path::PathBuf;

use tix_lsp::convert::LineIndex;
use tix_lsp::server::TixLanguageServer;
use tix_lsp::test_util::{parse_markers, TempProject};

/// Default timeout for waiting on diagnostics. The server has a 200ms
/// quiescence delay, so 5 seconds gives ample margin for CI.
pub const TIMEOUT: Duration = Duration::from_secs(5);

#[allow(dead_code)]
pub struct LspTestHarness {
    service: LspService<TixLanguageServer>,
    /// Buffered server→client notifications, drained by a background task.
    notif_rx: mpsc::UnboundedReceiver<Request>,
    next_id: AtomicI64,
    pub workspace: TempProject,
}

#[allow(dead_code)]
impl LspTestHarness {
    /// Create a harness with default stubs and the given initial files.
    pub async fn new(files: &[(&str, &str)]) -> Self {
        Self::with_options(files, true).await
    }

    /// Create a harness with control over stub loading.
    ///
    /// When `no_default_stubs` is true, built-in nixpkgs stubs are not loaded
    /// (faster, but hover results won't show lib types).
    pub async fn with_options(files: &[(&str, &str)], no_default_stubs: bool) -> Self {
        let workspace = TempProject::new(files);
        let root_dir = workspace.root_dir();
        let root_uri = Url::from_file_path(&root_dir).unwrap();

        let registry = if no_default_stubs {
            TypeAliasRegistry::new()
        } else {
            TypeAliasRegistry::with_builtins()
        };

        let (service, client_socket) = LspService::new(|client| {
            TixLanguageServer::new(client, registry, vec![], no_default_stubs)
        });

        // Spawn a background task to continuously drain the ClientSocket
        // stream into an unbounded channel. Without this, `Client::publish_diagnostics()`
        // blocks on the internal mpsc(1) channel after the first notification.
        let (notif_tx, notif_rx) = mpsc::unbounded_channel();
        tokio::spawn(async move {
            let mut stream = client_socket;
            while let Some(msg) = stream.next().await {
                // Forward all server→client messages; tests can filter as needed.
                let _ = notif_tx.send(msg);
            }
        });

        let mut harness = LspTestHarness {
            service,
            notif_rx,
            next_id: AtomicI64::new(1),
            workspace,
        };

        // Send initialize + initialized to get the server running.
        let init_request = Request::build("initialize")
            .params(json!({
                "capabilities": {},
                "rootUri": root_uri.as_str(),
            }))
            .id(harness.next_id())
            .finish();

        harness.send_request(init_request).await;

        let initialized = Request::build("initialized").params(json!({})).finish();
        harness.send_notification(initialized).await;

        harness
    }

    /// Create a harness rooted at an existing directory (e.g. nixpkgs lib/).
    ///
    /// Loads built-in stubs so lib type annotations are available. The
    /// directory is NOT deleted on drop — we don't own it.
    pub async fn with_root(root: PathBuf) -> Self {
        let workspace = TempProject::from_existing(root);
        let root_dir = workspace.root_dir();
        let root_uri = Url::from_file_path(&root_dir).unwrap();

        let registry = TypeAliasRegistry::with_builtins();

        let (service, client_socket) =
            LspService::new(|client| TixLanguageServer::new(client, registry, vec![], false));

        let (notif_tx, notif_rx) = mpsc::unbounded_channel();
        tokio::spawn(async move {
            let mut stream = client_socket;
            while let Some(msg) = stream.next().await {
                let _ = notif_tx.send(msg);
            }
        });

        let mut harness = LspTestHarness {
            service,
            notif_rx,
            next_id: AtomicI64::new(1),
            workspace,
        };

        let init_request = Request::build("initialize")
            .params(json!({
                "capabilities": {},
                "rootUri": root_uri.as_str(),
            }))
            .id(harness.next_id())
            .finish();

        harness.send_request(init_request).await;

        let initialized = Request::build("initialized").params(json!({})).finish();
        harness.send_notification(initialized).await;

        harness
    }

    fn next_id(&self) -> i64 {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }

    /// Low-level: send a JSON-RPC request and return the response.
    async fn send_request(&mut self, req: Request) -> Option<Response> {
        self.service
            .ready()
            .await
            .expect("service not ready")
            .call(req)
            .await
            .expect("service call failed")
    }

    /// Low-level: send a JSON-RPC notification (no response expected).
    async fn send_notification(&mut self, notif: Request) {
        let _ = self.service.ready().await.unwrap().call(notif).await;
    }

    // ==========================================================================
    // Document lifecycle
    // ==========================================================================

    /// Open a file by absolute path (for use with `from_existing` workspaces).
    pub async fn open_abs(&mut self, abs_path: &std::path::Path) {
        let uri = Url::from_file_path(abs_path).unwrap();
        let text = std::fs::read_to_string(abs_path).expect("read file for didOpen");

        let notif = Request::build("textDocument/didOpen")
            .params(json!({
                "textDocument": {
                    "uri": uri.as_str(),
                    "languageId": "nix",
                    "version": 1,
                    "text": text,
                }
            }))
            .finish();

        self.send_notification(notif).await;
    }

    /// Open a file (reads content from the TempProject on disk).
    pub async fn open(&mut self, name: &str) {
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();
        let text = std::fs::read_to_string(&path).expect("read file for didOpen");

        let notif = Request::build("textDocument/didOpen")
            .params(json!({
                "textDocument": {
                    "uri": uri.as_str(),
                    "languageId": "nix",
                    "version": 1,
                    "text": text,
                }
            }))
            .finish();

        self.send_notification(notif).await;
    }

    /// Send a full-text change for a file. Also writes the new text to disk
    /// so that `markers()` reads the updated content.
    pub async fn edit(&mut self, name: &str, new_text: &str) {
        self.workspace.write_file(name, new_text);
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();

        let notif = Request::build("textDocument/didChange")
            .params(json!({
                "textDocument": { "uri": uri.as_str(), "version": 2 },
                "contentChanges": [{ "text": new_text }]
            }))
            .finish();

        self.send_notification(notif).await;
    }

    /// Close a file.
    pub async fn close(&mut self, name: &str) {
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();

        let notif = Request::build("textDocument/didClose")
            .params(json!({
                "textDocument": { "uri": uri.as_str() }
            }))
            .finish();

        self.send_notification(notif).await;
    }

    // ==========================================================================
    // LSP requests
    // ==========================================================================

    /// Hover at a position in a file given by absolute path.
    pub async fn hover_abs(
        &mut self,
        abs_path: &std::path::Path,
        line: u32,
        character: u32,
    ) -> Option<Hover> {
        let uri = Url::from_file_path(abs_path).unwrap();

        let req = Request::build("textDocument/hover")
            .params(json!({
                "textDocument": { "uri": uri.as_str() },
                "position": { "line": line, "character": character }
            }))
            .id(self.next_id())
            .finish();

        let resp = self.send_request(req).await?;
        let (_id, result) = resp.into_parts();
        let value = result.ok()?;
        serde_json::from_value::<Hover>(value).ok()
    }

    /// Completions at a position in a file given by absolute path.
    pub async fn complete_abs(
        &mut self,
        abs_path: &std::path::Path,
        line: u32,
        character: u32,
    ) -> Option<CompletionResponse> {
        let uri = Url::from_file_path(abs_path).unwrap();

        let req = Request::build("textDocument/completion")
            .params(json!({
                "textDocument": { "uri": uri.as_str() },
                "position": { "line": line, "character": character }
            }))
            .id(self.next_id())
            .finish();

        let resp = self.send_request(req).await?;
        let (_id, result) = resp.into_parts();
        let value = result.ok()?;
        serde_json::from_value::<CompletionResponse>(value).ok()
    }

    /// Hover at a given line/character position.
    pub async fn hover(&mut self, name: &str, line: u32, character: u32) -> Option<Hover> {
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();

        let req = Request::build("textDocument/hover")
            .params(json!({
                "textDocument": { "uri": uri.as_str() },
                "position": { "line": line, "character": character }
            }))
            .id(self.next_id())
            .finish();

        let resp = self.send_request(req).await?;
        let (_id, result) = resp.into_parts();
        let value = result.ok()?;
        serde_json::from_value::<Hover>(value).ok()
    }

    /// Request completions at a given line/character position.
    pub async fn complete(
        &mut self,
        name: &str,
        line: u32,
        character: u32,
    ) -> Option<CompletionResponse> {
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();

        let req = Request::build("textDocument/completion")
            .params(json!({
                "textDocument": { "uri": uri.as_str() },
                "position": { "line": line, "character": character }
            }))
            .id(self.next_id())
            .finish();

        let resp = self.send_request(req).await?;
        let (_id, result) = resp.into_parts();
        let value = result.ok()?;
        serde_json::from_value::<CompletionResponse>(value).ok()
    }

    /// Go-to-definition at a given line/character position.
    pub async fn goto_def(
        &mut self,
        name: &str,
        line: u32,
        character: u32,
    ) -> Option<GotoDefinitionResponse> {
        let path = self.workspace.path(name);
        let uri = Url::from_file_path(&path).unwrap();

        let req = Request::build("textDocument/definition")
            .params(json!({
                "textDocument": { "uri": uri.as_str() },
                "position": { "line": line, "character": character }
            }))
            .id(self.next_id())
            .finish();

        let resp = self.send_request(req).await?;
        let (_id, result) = resp.into_parts();
        let value = result.ok()?;
        serde_json::from_value::<GotoDefinitionResponse>(value).ok()
    }

    // ==========================================================================
    // Diagnostics
    // ==========================================================================

    /// Wait for `publishDiagnostics` for a file given by absolute path.
    pub async fn wait_for_diagnostics_abs(
        &mut self,
        abs_path: &std::path::Path,
        timeout: Duration,
    ) -> Option<PublishDiagnosticsParams> {
        let expected_uri = Url::from_file_path(abs_path).unwrap();

        let deadline = tokio::time::Instant::now() + timeout;

        loop {
            match tokio::time::timeout_at(deadline, self.notif_rx.recv()).await {
                Ok(Some(msg)) => {
                    if msg.method() == "textDocument/publishDiagnostics" {
                        if let Some(params) = msg.params() {
                            if let Ok(diag_params) =
                                serde_json::from_value::<PublishDiagnosticsParams>(params.clone())
                            {
                                if diag_params.uri == expected_uri {
                                    return Some(diag_params);
                                }
                            }
                        }
                    }
                }
                Ok(None) => return None,
                Err(_) => return None,
            }
        }
    }

    /// Wait for a `publishDiagnostics` notification for the given file.
    /// Skips non-matching notifications (e.g. `window/logMessage`, diagnostics
    /// for other files). Returns `None` on timeout.
    pub async fn wait_for_diagnostics(
        &mut self,
        name: &str,
        timeout: Duration,
    ) -> Option<PublishDiagnosticsParams> {
        let path = self.workspace.path(name);
        let expected_uri = Url::from_file_path(&path).unwrap();

        let deadline = tokio::time::Instant::now() + timeout;

        loop {
            match tokio::time::timeout_at(deadline, self.notif_rx.recv()).await {
                Ok(Some(msg)) => {
                    if msg.method() == "textDocument/publishDiagnostics" {
                        if let Some(params) = msg.params() {
                            if let Ok(diag_params) =
                                serde_json::from_value::<PublishDiagnosticsParams>(params.clone())
                            {
                                if diag_params.uri == expected_uri {
                                    return Some(diag_params);
                                }
                            }
                        }
                    }
                    // Skip non-matching notifications and keep waiting.
                }
                Ok(None) => return None, // Channel closed.
                Err(_) => return None,   // Timeout.
            }
        }
    }

    /// Non-blocking drain of all buffered notifications. Returns all
    /// `publishDiagnostics` params found.
    pub fn drain_diagnostics(&mut self) -> Vec<PublishDiagnosticsParams> {
        let mut result = Vec::new();
        while let Ok(msg) = self.notif_rx.try_recv() {
            if msg.method() == "textDocument/publishDiagnostics" {
                if let Some(params) = msg.params() {
                    if let Ok(diag_params) =
                        serde_json::from_value::<PublishDiagnosticsParams>(params.clone())
                    {
                        result.push(diag_params);
                    }
                }
            }
        }
        result
    }

    // ==========================================================================
    // Markers
    // ==========================================================================

    /// Parse `# ^<num>` markers from a file and return `BTreeMap<u32, Position>`.
    ///
    /// Reads the file from disk, calls `parse_markers()` to get byte offsets,
    /// then maps each offset through `LineIndex` to get LSP positions.
    pub fn markers(&self, name: &str) -> BTreeMap<u32, Position> {
        let text = self.workspace.read_file(name);
        let byte_offsets = parse_markers(&text);
        let line_index = LineIndex::new(&text);

        byte_offsets
            .into_iter()
            .map(|(id, offset)| (id, line_index.position(offset)))
            .collect()
    }

    // ==========================================================================
    // Shutdown
    // ==========================================================================

    /// Send shutdown + exit. Call this at the end of each test for clean
    /// teardown (avoids "server not shut down" warnings).
    pub async fn shutdown(&mut self) {
        let shutdown = Request::build("shutdown").id(self.next_id()).finish();
        self.send_request(shutdown).await;

        let exit = Request::build("exit").finish();
        // After exit, service may return ExitedError — that's fine.
        let _ = self.service.call(exit).await;
    }
}
