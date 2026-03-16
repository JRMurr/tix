# Testing Gaps

Overall coverage: **83.39%** (8038/9639 lines) as of 2026-03-15.

## Tier 1: Significant Coverage Gaps in Core Logic

### `lang_check/collect.rs` — 75.6% (102 lines uncovered)

Canonicalization engine converting inference types to output types.

- [ ] Full integration through `canonicalize_concrete` for negation+intersection combinations
- [ ] Deadline-check branch inside `Canonicalizer` (requires timing-sensitive setup)

### `lang_check/lib.rs` — 56.8% (168 lines uncovered)

Public API and builder infrastructure.

- [ ] `CheckBuilder::from_inputs` and `CheckBuilder::from_precomputed` (LSP code paths)
- [ ] `CheckBuilder::rss_limit` setter and RSS-based early exit
- [ ] `DeferredConstraints::carried` — overload carry-over between SCC groups

### `lang_check/constrain.rs` — 79.6% (32 lines uncovered)

Core subtyping constraint function.

- [ ] `constrain_rhs_union` both-concrete no-tiebreak case (both union members match discriminant with sub — falls through to constrain-to-both)
- [ ] `constrain_concrete` with `Named` type on left/right in all combinations (Named nested in Inter/Union)
- [ ] `Concrete <: Neg(inner)` for non-primitive disjoint types (e.g. AttrSet <: ~List)

## Tier 2: Moderate Gaps

### `lang_ty/attrset.rs` — 35.7% (27 lines uncovered)

- [ ] `AttrSetTy::get_sub_set()` with optional fields propagation
- [ ] `AttrSetTy::get_sub_set()` panic path (missing key)
- [ ] `Ord` impl for `AttrSetTy<TyRef>` (used for sorting in canonicalization)

### `lsp/ty_nav.rs` — 69.2% (28 lines uncovered)

Type navigation helpers used by completion and hover.

- [ ] `get_module_config_type()` with `no-module` directive
- [ ] `get_module_config_type()` plain attrset module fallback (no lambda wrapper)
- [ ] `get_module_config_type()` lambda without pattern (plain lambda, not NixOS module)
- [ ] `collect_parent_attrpath_context()` — only tested indirectly via e2e completion
- [ ] `collect_attrpath_segments()` with `Str` attrs (string-literal keys like `"foo"` in attrpaths)

### `lang_check/diagnostic.rs` — 81.2% (26 lines uncovered)

- [ ] `Display` arms for rare `TixDiagnosticKind` variants

### `lang_check/imports.rs` — 80.4% (21 lines uncovered)

- [ ] Import cycle detection
- [ ] `nixpkgs:` URI resolution error paths
- [ ] Missing file error handling during import resolution

### `lsp/server.rs` — 76.5% (99 lines uncovered)

- [ ] Error handling paths in LSP request handlers
- [ ] Edge cases in `textDocument/didSave` and `textDocument/didClose`

### `lsp/completion.rs` — 78.4% (61 lines uncovered)

- [ ] Completion inside string interpolation
- [ ] Completion with dynamic attrpath keys
- [ ] Completion fallback paths when analysis is unavailable

### `lsp/lib.rs` — 8.2% (56 lines uncovered)

- [ ] Server initialization logic (mostly covered by e2e lifecycle test, but line coverage is very low — likely dead-code branches or cfg-gated paths)

### `lang_ast/lib.rs` — 60.8% (51 lines uncovered)

- [ ] `module_indices` edge cases: `Inherit` variant in binding_expr, patterns without names
- [ ] Various `Display`/`Debug` impls

## Tier 3: Weak or Shallow Tests

Tests that exist but don't assert enough:

- [ ] `has_field_with_default_no_error` (tests.rs:5612) — only checks no crash, no assertion on inferred type
- [ ] Several `error_case!` tests use `matches!` checking only the discriminant, not the field values (e.g. `MissingField` without checking `available` fields)
- [ ] PBT intersection-type tests only verify crash-freedom, not type correctness
- [ ] nixpkgs_lib integration test only checks crash-freedom, not that inferred types are sensible

## Tier 4: Missing Edge Case Categories

Entire feature areas with no dedicated test:

- [ ] **`Named` type unwrapping in constrain** for all combinations (Named on left, right, nested in Inter/Union)
- [ ] **Individual builtin signatures**: `builtins.rs` synthesizes types via `synth_ty!` for ~50 builtins, but no test validates individual signatures (only tested through integration when builtins are used in Nix code)
- [ ] **`narrow.rs` guard recognition unit tests**: `analyze_condition()` in `lang_ast/narrow.rs` has no unit tests — only tested via integration through `infer_with_narrowing()`

## Files With Zero Inline Tests

Tested only through integration. Consider adding focused unit tests for complex logic:

| File | Lines | Role |
|------|-------|------|
| `lang_check/infer.rs` | 1,376 | SCC iteration, extrude, generalization |
| `lang_check/storage.rs` | 157 | Type variable bounds storage |
| `lang_check/operators.rs` | 96 | Operator overload resolution |
| `lang_check/builtins.rs` | 365 | Builtin type synthesis |
| `lang_ast/narrow.rs` | 25,560 | Guard recognition, `analyze_condition()` |
| `lang_ast/comment.rs` | 4,271 | Comment/doc-comment extraction |
| `lang_ast/ast_utils.rs` | 2,099 | AST utility functions |
| `lsp/diagnostics.rs` | 205 | Diagnostic rendering |
