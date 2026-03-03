---
id: TASK-011
title: Investigate tower-lsp transport crash
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
labels:
  - bug
  - lsp
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Editing files in VS Code can trigger `unreachable!()` at `tower-lsp-0.20.0/src/transport.rs:120`. This is inside tower-lsp's message transport, not our code. Need to investigate whether upgrading tower-lsp or switching to a different LSP framework resolves it.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Determine root cause of the unreachable!() panic in tower-lsp transport
- [ ] #2 Either upgrade tower-lsp to a version with the fix, or switch framework, or work around the issue
- [ ] #3 LSP server does not crash during normal VS Code editing workflows
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
