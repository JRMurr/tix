---
id: TASK-009
title: 'LSP: did_change_configuration bypasses DashMap snapshots'
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
updated_date: '2026-03-03 03:03'
labels:
  - bug
  - lsp
  - concurrency
milestone: m-0
dependencies: []
references:
  - 'crates/lsp/src/server.rs:758-810'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
When stubs change via `did_change_configuration`, `reload_registry` runs analysis synchronously via the legacy `state.files` path. DashMap snapshots are never updated — handlers read stale data after a configuration change.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Configuration changes update DashMap snapshots so handlers see fresh data
- [ ] #2 Add test verifying handlers see updated state after configuration change
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
