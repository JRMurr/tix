---
id: TASK-007
title: 'LSP: Nested arg autocomplete doesn''t work'
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
updated_date: '2026-03-03 03:01'
labels:
  - bug
  - lsp
  - completion
milestone: m-0
dependencies: []
references:
  - TODO/Tasks.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Nested argument autocomplete doesn't work: `bubblewrap_helper { args = [ ] }` — cursor inside `args` list doesn't get element-type completions, only top-level attr keys. Top-level `bubblewrap_helper { }` works fine.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Completing inside a nested list argument (e.g. args = [ | ]) provides element-type completions
- [ ] #2 Top-level attrset completion continues to work
- [ ] #3 Add E2E test for nested argument completion
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
