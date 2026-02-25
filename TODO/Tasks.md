# Tix Pre-release Tasks

Tasks to address before wider adoption. Ordered by recommended priority —
earlier tasks protect against the worst user experiences or unblock later work.


1 - 11 and 16 should be done but need a good code review pass / testing

some manual notes

- arg auto complete seems to work for thing like bubble wrap helper but does not seem to work nested

ie 
```
foo = bubblewrap_helper {   }
#                         ^ i get all the attrs to the call as autocomplete



bar = bubblewrap_helper { args = [ ]  }
#                                 ^ i just get top level attr keys not autocomplete for elements of args
```

- dot autocomplete does not show at all automatically

in `foo = lib.` i need to hit control + space to see autocomplete. 
I assume its the debounce somehow not triggering the auto complete event? Maybe we should just lower the debounce?
We should we just do w/e rust analyzer does cuz it feels good for it. Maybe we can pre-compute autocomplete as you are typing lib or something?

EDIT: actually it worked automatically now?? seems sus need some better testing maybe


---

## 1. Add CI pipeline for tests/clippy/fmt

**Effort**: Low | **Impact**: Critical

Only a docs deployment workflow exists. A contributor (or you) can push a broken
build with no feedback.

**What to do**:

1. Add `.github/workflows/ci.yml` that runs on PRs and pushes to `main`.
2. Jobs: `cargo fmt --check`, `cargo clippy -- -D warnings`, `cargo test`.
3. Consider adding `./scripts/pbt.sh 10000` as a separate slower job.
4. Consider `nix build .#` to verify the flake builds.

**Files touched**: `.github/workflows/ci.yml`

---

## 2. Convert `.tix` stub parsing panics to Result-based errors

**Effort**: Medium | **Impact**: Critical

`comment_parser/src/tix_collect.rs` and `comment_parser/src/collect.rs` use
`panic!()` / `unreachable!()` (~13 sites) when parsing user-provided `.tix`
files. A typo in a stub file crashes the CLI or LSP with no useful message.

**What to do**:

1. Define an error type in `comment_parser` for stub parse errors (with span
   info where available).
2. Replace `panic!("expected TypeAlias, got: ...")` and similar calls with
   `Result::Err(...)`.
3. Propagate errors up through `parse_tix_file` and callers in `cli/` and
   `lsp/`.
4. Surface stub parse errors as CLI stderr messages and LSP diagnostics.
5. Add tests for malformed `.tix` input (missing semicolons, bad types, etc.).

**Files touched**: `comment_parser/src/tix_collect.rs`,
`comment_parser/src/collect.rs`, `comment_parser/src/lib.rs`,
`lang_check/src/aliases.rs`, `cli/src/main.rs`, `lsp/src/state.rs`

---

## 3. Surface import resolution errors as LSP diagnostics

**Effort**: Low | **Impact**: Critical

`lsp/src/state.rs:154` — import errors are logged but never shown to the user.
When `import ./missing.nix` fails, the user sees no feedback; they just get
missing type info with no explanation.

**What to do**:

1. Collect `import_resolution.errors` after inference.
2. Convert each to an LSP `Diagnostic` with the import expression's span.
3. Merge with existing type diagnostics before publishing.
4. Add a test in `lsp/src/` that verifies a missing-import diagnostic appears.

**Files touched**: `lsp/src/state.rs`, `lsp/src/diagnostics.rs`

---

## 4. Replace `.expect()` in CLI output path with user-facing error

**Effort**: Trivial | **Impact**: High

`cli/src/main.rs:392` — `expect("No type for root module entry")` will panic if
inference doesn't populate the root entry. Should print a clean error message.

**What to do**:

1. Replace `.expect(...)` with a match or `.ok_or_else(...)` that prints a
   message like `"error: could not infer type for root expression"` and exits
   with code 1.

**Files touched**: `cli/src/main.rs`

---

## 5. Add diagnostic for duplicate attrset keys

**Effort**: Medium | **Impact**: High

`lang_ast/src/lower.rs:498` — duplicate keys in attrsets silently overwrite.
This is a real bug-catching opportunity that other Nix tools provide.

**What to do**:

1. Add a `DuplicateKey { key, first_span, second_span }` diagnostic kind.
2. In `merge_static_bindings` (lower.rs), when a key is overwritten, emit the
   diagnostic with both spans.
3. Propagate through to CLI and LSP output.
4. Severity: Warning (Nix allows it, but it's almost always a mistake).
5. Add regression tests.

**Files touched**: `lang_ast/src/lower.rs`, `lang_ast/src/lib.rs` (or
diagnostic types), `lang_check/src/diagnostic.rs`, test files

---

## 6. Surface inference timeout as a diagnostic

**Effort**: Low-Medium | **Impact**: High

When inference hits the deadline (5s imports, 10s top-level), the user gets no
types and no explanation why. They should see a diagnostic like "type inference
timed out for this binding; consider adding a type annotation."

**What to do**:

1. When `check_file_collecting_with_deadline` returns partial results due to
   timeout, identify which bindings lack types.
2. Emit a diagnostic at the binding site explaining the timeout.
3. In LSP, surface these as Warning-level diagnostics.
4. In CLI, print to stderr.

**Files touched**: `lang_check/src/infer.rs`, `lsp/src/state.rs`,
`cli/src/main.rs`, `lang_check/src/diagnostic.rs`

---

## 7. LSP request debouncing and cancellation

**Effort**: High | **Impact**: High

SESSION.md documents that the LSP blocks on large repos due to serial `didOpen`
processing with no debouncing or cancellation. Opening a large flake project
freezes the editor.

**What to do**:

1. Add a debounce delay for `didChange` / `didOpen` notifications (e.g., 300ms).
2. Support cancellation: when a new edit arrives, cancel in-flight analysis for
   the same file.
3. Consider using `tokio::select!` or a cancellation token passed into inference.
4. The existing deadline mechanism helps, but cancellation avoids waiting for
   the full timeout.

**Files touched**: `lsp/src/state.rs`, `lsp/src/server.rs`

---

## 8. Fix multi-`with` environment fallthrough

**Effort**: Medium-High | **Impact**: High

Only the innermost `with` scope is constrained. Nested `with pkgs; with lib;
someFunc` won't resolve `someFunc` from the outer scope when the inner scope
lacks it. This is extremely common Nix code.

**What to do**:

1. In `infer_expr.rs`, the `With` handling needs to try the inner `with` env
   first, then fall through to outer `with` envs for unresolved names.
2. This requires tracking a stack of `with` environments rather than a single
   override.
3. See `lang_check/src/tests.rs:888` for the existing test that documents this
   limitation.
4. Add regression tests for nested `with` scopes.

**Files touched**: `lang_check/src/infer_expr.rs`, `lang_check/src/tests.rs`,
`lang_ast/src/nameres.rs`

---

## 9. Implement LSP signature help

**Effort**: Medium | **Impact**: High

No `textDocument/signatureHelp` is implemented. Users expect to see parameter
names and types when calling functions — this is arguably the biggest win a
type-checker LSP provides over a plain language server.

**What to do**:

1. Add a `textDocument/signatureHelp` handler in `lsp/src/`.
2. When the cursor is inside a function application, look up the function's
   inferred type.
3. For lambda types with pattern parameters, show the expected fields and their
   types.
4. For curried functions, show which parameter position the cursor is at.
5. Register the capability in `server.rs` server capabilities.
6. Add tests using marker-based positioning.

**Files touched**: new `lsp/src/signature_help.rs`, `lsp/src/server.rs`

---

## 10. Cross-file rename warning/support

**Effort**: Medium | **Impact**: Medium

`lsp/src/rename.rs:71` — rename only works within a single file. Renaming an
exported binding won't update importers.

**What to do**:

1. At minimum: detect when a renamed binding is the target of imports from other
   open files and warn the user.
2. Stretch: scan open files for `import` expressions pointing at the current
   file and update references.
3. Add tests.

**Files touched**: `lsp/src/rename.rs`, `lsp/src/state.rs`

---

## 11. Implement workspace symbol search

**Effort**: Medium | **Impact**: Medium

No `workspace/symbol` handler. Users can't search for a function name across
their project from the LSP.

**What to do**:

1. Add a `workspace/symbol` handler.
2. Aggregate document symbols from all open/analyzed files.
3. Support fuzzy matching on the query string.
4. Register the capability in server capabilities.

**Files touched**: new `lsp/src/workspace_symbols.rs`, `lsp/src/server.rs`

---

## 12. Union constraint snapshot/rollback

**Effort**: High | **Impact**: Medium

`lang_check/src/constrain.rs:474` — union constraint routing is
over-constraining when multiple paths exist. Correct implementation needs state
snapshots to try each union branch independently.

**What to do**:

1. Read the TODO at `constrain.rs:474` and understand the current behavior.
2. Implement snapshot/rollback for `TypeStorage` bounds.
3. When constraining against a union, try each branch with a snapshot; if one
   succeeds, commit it; if all fail, report the error.
4. This is a correctness fix — false positives on real code using
   `if x then A else B` patterns with complex unions.
5. Add regression tests for the specific false-positive patterns.

**Files touched**: `lang_check/src/constrain.rs`, `lang_check/src/storage.rs`,
`lang_check/src/tests.rs`

---

## 13. Add troubleshooting / FAQ documentation page

**Effort**: Low | **Impact**: Medium

Users who hit limitations (deadline timeouts, missing narrowing, `with` issues)
have no guide for workarounds. Reduces support burden.

**What to do**:

1. Add `docs/src/troubleshooting.md`.
2. Add it to `docs/src/SUMMARY.md`.
3. Cover common issues:
   - "Why did I get no types?" → inference timeout, add annotations
   - "Why doesn't `with` work?" → nested `with` limitation
   - "How do I type an imported library?" → stubs and doc comments
   - "Why is my attrset field missing?" → open vs closed sets
   - Common LSP setup issues

**Files touched**: `docs/src/troubleshooting.md`, `docs/src/SUMMARY.md`

---

## 14. Improve nixpkgs lib stub coverage

**Effort**: Medium | **Impact**: Medium

~200 nixpkgs lib functions lack noogle signatures. Users hitting unstubbed lib
functions get `⊤` types with no explanation.

**What to do**:

1. Review `scripts/gen_lib_stubs.py` and identify why some functions are missed.
2. Add manual stubs for the most commonly used functions that noogle misses.
3. Consider adding a diagnostic when a stub lookup returns `⊤` for a known lib
   path — "no type stub available for `lib.foo`".
4. All changes go through `scripts/gen_lib_stubs.py` so regeneration preserves
   fixes.

**Files touched**: `scripts/gen_lib_stubs.py`, `stubs/lib.tix`

---

## 15. Make narrowing guard list extensible via stubs

**Effort**: Medium | **Impact**: Medium

`lang_ast/src/narrow.rs:89` — type narrowing guards are hardcoded. Third-party
libraries can't declare their own type guards.

**What to do**:

1. Add an `@inline` or `@narrows` annotation in `.tix` stub syntax.
2. When loading stubs, register annotated functions as narrowing guards.
3. Update `analyze_condition` to check the registry in addition to hardcoded
   builtins.
4. Update `.tix` syntax documentation in the mdbook.

**Files touched**: `lang_ast/src/narrow.rs`, `comment_parser/src/tix_decl.pest`,
`comment_parser/src/tix_collect.rs`, `docs/src/stubs.md`

---

## 16. Implement basic code actions

**Effort**: High | **Impact**: Medium

No `textDocument/codeAction` support. High-value quick fixes for a type checker:

**Candidates** (implement incrementally):

1. "Add missing field" — when a `MissingField` diagnostic exists, offer to add
   the field with a placeholder value.
2. "Add type annotation" — offer to insert a doc comment annotation for a
   binding.
3. "Remove unused binding" — when a binding has no references.

**Files touched**: new `lsp/src/code_actions.rs`, `lsp/src/server.rs`

