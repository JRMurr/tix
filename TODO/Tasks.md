# Tix Pre-release Tasks

Remaining tasks to address before wider adoption.

## Manual notes

- Nested arg autocomplete doesn't work: `bubblewrap_helper { args = [ ] }` —
  cursor inside `args` list doesn't get element-type completions, only top-level
  attr keys. Top-level `bubblewrap_helper { }` works fine.

- Dot autocomplete sometimes requires Ctrl+Space instead of triggering
  automatically on `.`. Inconsistent behavior — needs investigation.

---

## 1. Convert `tix_collect.rs` panics to Result-based errors

**Effort**: Medium | **Impact**: Critical

`comment_parser/src/tix_collect.rs` has 21+ `panic!()` calls in parser tree
match arms (e.g. `other => panic!("expected TypeAlias, got: {other:?}")`).
A typo in a `.tix` stub file crashes the CLI or LSP with no useful message.

Note: `collect.rs` was already converted to `Result<_, CollectError>`.

**What to do**:

1. Extend `CollectError` to cover `tix_collect.rs` failure modes.
2. Replace `panic!("expected X, got: ...")` calls with `Result::Err(...)`.
3. Propagate errors up through `parse_tix_file` and callers.
4. Surface stub parse errors as CLI stderr messages and LSP diagnostics.
5. Add tests for malformed `.tix` input.

**Files touched**: `comment_parser/src/tix_collect.rs`,
`lang_check/src/aliases.rs`, `cli/src/main.rs`, `lsp/src/state.rs`

---

## 2. Union constraint snapshot/rollback

**Effort**: High | **Impact**: Medium

`lang_check/src/constrain.rs` — union constraint routing is over-constraining
when multiple paths exist. Correct implementation needs state snapshots to try
each union branch independently.

**What to do**:

1. Read the TODO at `constrain.rs:474` and understand the current behavior.
2. Implement snapshot/rollback for `TypeStorage` bounds.
3. When constraining against a union, try each branch with a snapshot; if one
   succeeds, commit it; if all fail, report the error.
4. This is a correctness fix — false positives on real code.
5. Add regression tests.

**Files touched**: `lang_check/src/constrain.rs`, `lang_check/src/storage.rs`,
`lang_check/src/tests.rs`

---

## 3. Make narrowing guard list extensible via stubs

**Effort**: Medium | **Impact**: Medium

`lang_ast/src/narrow.rs:89` — type narrowing guards are hardcoded. Third-party
libraries can't declare their own type guards. There's a TODO in the code
describing the approach.

**What to do**:

1. Add an `@inline` annotation in `.tix` stub syntax.
2. When loading stubs, register annotated functions as narrowing guards.
3. Update `analyze_condition` to check the registry in addition to hardcoded
   builtins.
4. Update `.tix` syntax documentation in the mdbook.

**Files touched**: `lang_ast/src/narrow.rs`, `comment_parser/src/tix_decl.pest`,
`comment_parser/src/tix_collect.rs`, `docs/src/stubs.md`

---

## 4. Improve nixpkgs lib stub coverage

**Effort**: Medium | **Impact**: Medium

~200 nixpkgs lib functions lack noogle signatures. Users hitting unstubbed lib
functions get `⊤` types with no explanation. `scripts/gen_lib_stubs.py` has been
substantially improved (manual overrides for lists, attrsets, strings, options,
modules, types) but gaps remain.

**What to do**:

1. Identify the most commonly used functions still missing stubs.
2. Add manual overrides in `scripts/gen_lib_stubs.py`.
3. Consider a diagnostic when a stub lookup returns `⊤` for a known lib path.

**Files touched**: `scripts/gen_lib_stubs.py`, `stubs/lib.tix`
