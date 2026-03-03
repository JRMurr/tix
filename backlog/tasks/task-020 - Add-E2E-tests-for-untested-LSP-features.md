---
id: TASK-020
title: Add E2E tests for untested LSP features
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-03 03:08'
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
- [ ] #1 E2E tests for go-to-definition, references, and rename
- [ ] #2 E2E tests for signature help and inlay hints
- [ ] #3 E2E tests for document symbols and workspace symbols
- [ ] #4 E2E tests for semantic tokens, selection range, and document highlight
- [ ] #5 Tests use LspTestHarness and marker-based positioning
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
