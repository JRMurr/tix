---
id: TASK-020
title: Add E2E tests for untested LSP features
status: Done
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-05 01:30'
labels:
  - test-coverage
  - lsp
milestone: m-0
dependencies: []
references:
  - crates/lsp/tests/common/mod.rs
  - crates/lsp/tests/e2e_*.rs
  - 'TODO/code_review.md (item #28)'
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
13 LSP features lack E2E protocol-level tests: go-to-definition, references, rename, signature help, inlay hints, document symbols, workspace symbols, semantic tokens, selection range, document highlight, document links, code actions, and formatting.

Tests should use the existing `LspTestHarness` in `lsp/tests/common/mod.rs` and follow marker-based positioning conventions from `test_util.rs`.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 E2E tests for go-to-definition, references, and rename
- [x] #2 E2E tests for signature help and inlay hints
- [x] #3 E2E tests for document symbols and workspace symbols
- [x] #4 E2E tests for semantic tokens, selection range, and document highlight
- [x] #5 Tests use LspTestHarness and marker-based positioning
- [x] #6 E2E tests for code actions (missing field quick fix, remove unused binding)
- [x] #7 E2E tests for document links and formatting
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented 23 E2E protocol-level tests across 13 new test files, covering all previously untested LSP features. Added 13 harness methods to `LspTestHarness` in `common/mod.rs`.\n\n**New test files (23 tests total):**\n- `e2e_goto_def.rs` — same-file + cross-file go-to-definition (2 tests)\n- `e2e_references.rs` — include/exclude declaration (2 tests)\n- `e2e_rename.rs` — prepare_rename, single-file, cross-file (3 tests)\n- `e2e_signature_help.rs` — simple + curried functions (2 tests)\n- `e2e_inlay_hints.rs` — non-trivial bindings + temporal update (2 tests)\n- `e2e_document_symbols.rs` — let-bindings + nested attrsets (2 tests)\n- `e2e_workspace_symbols.rs` — cross-file + query filtering (2 tests)\n- `e2e_semantic_tokens.rs` — non-empty delta-encoded data (1 test)\n- `e2e_selection_range.rs` — parent chain + multiple positions (2 tests)\n- `e2e_document_highlight.rs` — WRITE/READ kind distinction (1 test)\n- `e2e_code_actions.rs` — missing field quick fix + remove unused (2 tests)\n- `e2e_document_links.rs` — import produces link (1 test)\n- `e2e_formatting.rs` — nixfmt produces edits (1 test)\n\nAll 264 LSP tests pass. No clippy warnings in new code.
<!-- SECTION:FINAL_SUMMARY:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [x] #1 tests + lints pass
- [x] #2 Documentation updated
- [x] #3 No test regressions
- [x] #4 Feature has test coverage
<!-- DOD:END -->
