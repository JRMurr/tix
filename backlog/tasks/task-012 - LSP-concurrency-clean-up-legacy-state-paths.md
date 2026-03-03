---
id: TASK-012
title: 'LSP concurrency: clean up legacy state paths'
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
updated_date: '2026-03-03 03:04'
labels:
  - tech-debt
  - lsp
  - concurrency
milestone: m-0
dependencies:
  - TASK-009
references:
  - SESSION.md
  - crates/lsp/src/state.rs
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The Salsa concurrency migration is structurally complete (DashMap snapshots, split Phase A/B mutex, cancel flag, parallel rayon imports). Remaining cleanup:

- Legacy `pending_text` / `state.files` still exist alongside DashMap snapshots
- hover/completion still lock state briefly for DocIndex (should store separately)
- goto_def/rename cross-file still lock state for Salsa DB access
- Regression tests for import cap, aggregate deadline, canonicalization deadline, and cancel flag in Salsa path are not yet written.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Remove legacy pending_text / state.files code paths in favor of DashMap snapshots
- [ ] #2 DocIndex stored separately so hover/completion don't lock state
- [ ] #3 goto_def/rename cross-file don't require state lock for Salsa DB access
- [ ] #4 Add regression tests for import cap, aggregate deadline, canonicalization deadline, and cancel flag
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
