---
id: TASK-008
title: 'LSP: Dot autocomplete sometimes requires Ctrl+Space'
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
labels:
  - bug
  - lsp
  - completion
dependencies: []
references:
  - TODO/Tasks.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Dot autocomplete sometimes requires Ctrl+Space instead of triggering automatically on `.`. Inconsistent behavior — needs investigation to determine root cause.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Dot completion triggers automatically when typing '.' after an identifier
- [ ] #2 Identify and fix the root cause of inconsistent trigger behavior
- [ ] #3 Add E2E test for dot-triggered completion
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
