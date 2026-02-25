# LSP Integration Test Harness

## Problem

All 19 LSP test modules call handler functions directly (e.g.
`completion(analysis, pos, ...)`) — no JSON-RPC, no async runtime, no
server lifecycle. The PBT in `pbt.rs` only checks crash freedom. Bugs in
message routing, initialization sequencing, notification handling, the
async analysis loop, diagnostic coalescing, stale-analysis completion
fallback, and `didChange` → analysis → `publishDiagnostics` flow are
completely untested.

## Approach: In-process duplex stream harness

Wire `tokio::io::duplex` channels into `tower_lsp::Server`, speak the
real Content-Length-framed JSON-RPC protocol, but stay in-process (no
subprocess, no stdio). This is the approach used by
[earthlyls](https://github.com/glehmann/earthlyls/blob/main/tests/common/mod.rs)
and
[ast-grep](https://github.com/ast-grep/ast-grep/blob/main/crates/lsp/tests/basic.rs).

Why not the other options:

- **`tower::Service::call` on `LspService`**: The `ClientSocket` isn't
  connected, so `publishDiagnostics` and other server→client messages go
  nowhere. Can't test the analysis loop, diagnostic coalescing, or
  notification flows.
- **Subprocess spawn + stdio**: Overkill. Harder to debug. Same protocol
  coverage as duplex streams with more moving parts.
- **Testing at the handler level only** (what we do now): Misses the
  entire server lifecycle and async wiring layer where bugs hide.

### How rust-analyzer and nil do it (and why we diverge)

rust-analyzer and nil both test at an `ide` crate API boundary. The LSP
layer is kept deliberately thin — just type translation — so it doesn't
warrant its own tests. Their `ide` crate exposes a Rust API with
`Fixture` parsers that create in-memory multi-file workspaces:

```rust
// rust-analyzer style (simplified)
let analysis = fixture::file("let x: i32 = $0;");
let hover = analysis.hover(pos).unwrap();
expect![[r#"i32"#]].assert_eq(&hover.info);
```

nil (by oxalica, also a Nix LSP) follows the same structure with a
Salsa-backed `TestDB`, `$0`/`$1` position markers, and all testing at
the `ide` level.

This works for them because their LSP layers are trivial adapters. **Tix
is different** — `TixLanguageServer` has meaningful async behavior:

- Event coalescing in `spawn_analysis_loop` (rapid edits collapse)
- Diagnostic quiescence timer (200ms debounce before publishing)
- Stale-analysis completion fallback (`pending_text` + fresh re-parse)
- Cancellation via `Arc<AtomicBool>` when new edits arrive mid-analysis
- `didChangeConfiguration` triggering registry reload + re-analysis

These are real bug surfaces that only exist in the server wiring layer,
so we need protocol-level tests.

## Implementation plan

### 1. Add test dependencies to `crates/lsp/Cargo.toml`

```toml
[dev-dependencies]
tokio = { version = "1", features = ["full", "test-util"] }
tokio-util = { version = "0.7", features = ["codec"] }
serde_json = "1"
```

`tower-lsp` already provides `lsp_types`, `jsonrpc`, and `Server`.
`tokio` is already a dependency; we just need `test-util` for
`tokio::time::pause()` (lets us control the diagnostic quiescence timer
deterministically without real sleeps).

### 2. Create `crates/lsp/tests/common/mod.rs` — the test harness

~150-200 lines. Three components:

#### 2a. `LspCodec` — Content-Length framing codec

Implement `tokio_util::codec::{Decoder, Encoder}` for
`serde_json::Value`. This handles the `Content-Length: N\r\n\r\n{json}`
framing that LSP requires.

ast-grep's implementation is the reference. Key property: `Decoder`
returns `Ok(None)` when the buffer doesn't yet contain a complete
message, so `Framed` handles partial reads correctly.

```rust
struct LspCodec;

impl Decoder for LspCodec {
    type Item = serde_json::Value;
    type Error = io::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        // Find "Content-Length: " header
        // Parse length
        // Check if full body is available
        // If yes: deserialize JSON, split_to() consumed bytes, return Some
        // If no: return None (wait for more data)
    }
}

impl Encoder<serde_json::Value> for LspCodec {
    type Error = io::Error;

    fn encode(&mut self, item: Value, dst: &mut BytesMut) -> Result<(), Self::Error> {
        let json = serde_json::to_string(&item)?;
        dst.put(format!("Content-Length: {}\r\n\r\n{}", json.len(), json).as_bytes());
        Ok(())
    }
}
```

Unit test the codec with a roundtrip property test.

#### 2b. `TestContext` — typed client wrapper

Wraps a `Framed<DuplexStream, LspCodec>` with typed helper methods.

```rust
struct TestContext {
    stream: Framed<DuplexStream, LspCodec>,
    server_handle: JoinHandle<()>,
    next_id: AtomicI64,
    workspace: TempDir,
}
```

**Construction:**
- Build `LspService` with `TixLanguageServer::new(client, registry, ...)`
- Create one `duplex(16384)` pair, `split()` the server end for
  `Server::new(read, write, socket)`
- Wrap client end in `Framed::new(client_stream, LspCodec)`
- `tokio::spawn` the server
- Copy fixture files to a `TempDir` workspace

**Core methods:**

| Method | Behavior |
|--------|----------|
| `request<R: lsp_types::request::Request>(params) -> R::Result` | Build JSON-RPC request with auto-incremented ID, send, read response (skipping notifications), deserialize |
| `notify<N: lsp_types::notification::Notification>(params)` | Send notification (no ID, no response) |
| `initialize()` | Send `initialize` + `initialized` with realistic capabilities |
| `open(path, text)` | Send `textDocument/didOpen` for a file in the workspace |
| `change(path, text)` | Send `textDocument/didChange` (full sync) |
| `close(path)` | Send `textDocument/didClose` |
| `wait_for_diagnostics(uri) -> Vec<Diagnostic>` | Read messages until `publishDiagnostics` for the given URI, with timeout |
| `drain_notifications() -> Vec<Value>` | Non-blocking drain of all pending server notifications |
| `doc_uri(relative_path) -> Url` | Build `file://` URI rooted at workspace |

**Notification handling strategy** (learn from both reference projects):

- `response()` (called by `request()`) loops reading messages:
  - If it's a response matching our request ID → return it
  - If it's `window/logMessage` → skip
  - If it's `client/registerCapability` → auto-respond with success
  - If it's `publishDiagnostics` → stash in a `Vec` for
    `wait_for_diagnostics` to return later
  - Everything else → stash for `drain_notifications`
- Use `tokio::time::timeout(Duration::from_secs(5), ...)` on every read
  to prevent hangs in CI

#### 2c. Fixture helpers

- `TestContext::with_stubs(stubs: &str, files: &[(&str, &str)])` —
  creates workspace with `.tix` stubs and multiple `.nix` files
- `TestContext::simple(src: &str)` — single-file shortcut (creates
  `test.nix` with the given source)

### 3. Create `crates/lsp/tests/integration.rs` — the test file

Start with tests that exercise the server lifecycle and async behavior
that unit tests can't reach:

#### Phase 1: Server lifecycle & diagnostics

```rust
#[tokio::test]
async fn initialize_returns_capabilities() {
    let ctx = TestContext::simple("1").await;
    // initialize() already called in constructor
    // Verify returned capabilities match expected set
}

#[tokio::test]
async fn diagnostics_on_open_unresolved_name() {
    let ctx = TestContext::simple("let x = 1; in y").await;
    ctx.open("test.nix", "let x = 1; in y").await;
    let diags = ctx.wait_for_diagnostics("test.nix").await;
    assert!(diags.iter().any(|d| d.message.contains("unresolved")));
}

#[tokio::test]
async fn diagnostics_cleared_on_close() {
    let ctx = TestContext::simple("let x = 1; in y").await;
    ctx.open("test.nix", "let x = 1; in y").await;
    ctx.wait_for_diagnostics("test.nix").await;
    ctx.close("test.nix").await;
    let diags = ctx.wait_for_diagnostics("test.nix").await;
    assert!(diags.is_empty());
}

#[tokio::test]
async fn diagnostics_update_after_edit() {
    let ctx = TestContext::simple("").await;
    ctx.open("test.nix", "let x = 1; in y").await;
    ctx.wait_for_diagnostics("test.nix").await; // has errors

    ctx.change("test.nix", "let x = 1; in x").await;
    let diags = ctx.wait_for_diagnostics("test.nix").await;
    assert!(diags.is_empty()); // errors gone
}
```

#### Phase 2: Feature requests through the protocol

```rust
#[tokio::test]
async fn hover_shows_type() {
    let ctx = TestContext::simple("let x = 1; in x").await;
    ctx.open("test.nix", "let x = 1; in x").await;
    ctx.wait_for_diagnostics("test.nix").await; // wait for analysis

    let hover = ctx.request::<HoverRequest>(HoverParams {
        text_document_position_params: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: ctx.doc_uri("test.nix") },
            position: Position { line: 0, character: 15 }, // the `x` after `in`
        },
        work_done_progress_params: Default::default(),
    }).await;

    assert!(hover.is_some());
    // Check that hover content mentions "int"
}

#[tokio::test]
async fn completion_after_dot() {
    let ctx = TestContext::simple("").await;
    ctx.open("test.nix", "let lib = { x = 1; }; in lib.").await;
    ctx.wait_for_diagnostics("test.nix").await;

    let completions = ctx.request::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: ctx.doc_uri("test.nix") },
            position: Position { line: 0, character: 29 }, // after the dot
        },
        ..Default::default()
    }).await;

    let items = match completions.unwrap() {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };
    assert!(items.iter().any(|i| i.label == "x"));
}

#[tokio::test]
async fn goto_definition_cross_file() {
    let ctx = TestContext::with_files(&[
        ("main.nix", "let lib = import ./lib.nix; in lib.foo"),
        ("lib.nix", "{ foo = 42; }"),
    ]).await;
    ctx.open("main.nix", "...").await;
    ctx.open("lib.nix", "...").await;
    ctx.wait_for_diagnostics("main.nix").await;

    let def = ctx.request::<GotoDefinition>(/* position of `foo` */).await;
    // Assert it points to lib.nix
}
```

#### Phase 3: Async behavior specific to tix

These are the tests that **only** a protocol-level harness can provide:

```rust
#[tokio::test]
async fn stale_completion_uses_fresh_parse() {
    // Open file, wait for analysis
    // Immediately send didChange + completion request
    // Verify completion works even before re-analysis completes
    // (exercises the pending_text + fresh re-parse path)
}

#[tokio::test]
async fn rapid_edits_coalesce() {
    // Send many didChange notifications in rapid succession
    // Wait for diagnostics
    // Verify we get diagnostics for the FINAL text, not intermediate
}

#[tokio::test]
async fn config_change_reloads_stubs() {
    // Start with no stubs
    // Send didChangeConfiguration with a stubs path
    // Verify diagnostics change (previously unresolved names resolve)
}

#[tokio::test]
async fn analysis_cancellation_on_new_edit() {
    // Open a file that takes a while to analyze (complex nix)
    // Immediately send a didChange
    // Verify we eventually get correct diagnostics for the new text
    // (exercises the cancel flag path)
}
```

#### Phase 4: PBT at the protocol level

Extend `pbt.rs`-style crash freedom testing to the protocol layer:

```rust
proptest! {
    #[test]
    fn protocol_crash_freedom(src in arb_nix_expr()) {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let ctx = TestContext::simple("").await;
            ctx.open("test.nix", &src).await;
            // Don't assert on content — just verify the server
            // doesn't crash, hang, or return malformed JSON-RPC
            let _ = tokio::time::timeout(
                Duration::from_secs(5),
                ctx.wait_for_diagnostics("test.nix"),
            ).await;
        });
    }
}
```

### 4. CI integration

Add the integration tests to the test matrix. They should run with
`cargo test --package lsp --test integration`. Consider marking the
slower PBT tests with `#[ignore]` and running them separately (like the
existing `./scripts/pbt.sh` pattern).

## Reference implementations

### earthlyls `TestContext` (~150 lines)

**Repo**: `github.com/glehmann/earthlyls`, file `tests/common/mod.rs`

- Two `duplex(1024)` pairs (separate request/response channels)
- Manual framing with `BufReader::read_line` + `read_exact`
- Typed `request::<R>(params) -> R::Result` and `notify::<N>(params)`
  using `tower_lsp::lsp_types::request::Request` trait (method name,
  params type, result type all linked at compile time)
- Auto-incrementing request IDs (per-TestContext `i64`)
- Copies fixture directories from `tests/workspace/{name}/` to `TempDir`
- Notification skip loop: silently discards `window/logMessage`, panics
  on anything else unexpected
- **No timeouts** — tests hang if server doesn't respond. Fine for their
  simple server; risky for tix's async analysis loop

### ast-grep LSP tests (~500 lines)

**Repo**: `github.com/ast-grep/ast-grep`, file
`crates/lsp/tests/basic.rs`

- Single `duplex(16384)` pair, `split()` for server end
- `tokio_util::codec::Framed` with custom `LspCodec`
  (Decoder/Encoder) — properly handles partial reads via `Ok(None)`
- Raw `serde_json::Value` everywhere (less type-safe than earthlyls)
- Global `AtomicI32` for request IDs (safe across parallel tests)
- `wait_for_diagnostics()` with bounded retry (20 iterations) and
  per-message timeout (`tokio::time::timeout(Duration::from_secs(2))`)
- Handles server-initiated requests inline (e.g. responds to
  `workspace/workspaceFolders`)
- Tests cover: init handshake, didOpen → diagnostics, codeAction
  request, workspace edit application, file watcher registration

### Design choices for tix harness

Take the best of both:

| Aspect | Choice | Rationale |
|--------|--------|-----------|
| Framing | `tokio_util::codec::Framed` + `LspCodec` | Handles partial reads correctly; one fewer dependency than BufReader approach |
| Stream topology | Single duplex + `split()` | Simpler, matches ast-grep |
| Type safety | Use `lsp_types::request::Request` trait like earthlyls | Catches protocol mismatches at compile time |
| Timeouts | 5-second per-read timeout | Prevents CI hangs. Tix's analysis loop has real async delays |
| Notification handling | Stash diagnostics, auto-respond to `registerCapability`, skip `logMessage` | Tix sends all of these |
| Request IDs | Global `AtomicI64` | Safe for `#[tokio::test]` parallel execution |
| Fixtures | `TempDir` with programmatic file creation | No need for fixture directories; Nix sources are short |
| Time control | `tokio::time::pause()` for quiescence timer tests | Lets us test the 200ms diagnostic debounce without real sleeps |
