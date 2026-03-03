---
id: TASK-006
title: Overloaded operators don't survive file boundaries
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
updated_date: '2026-03-03 02:58'
labels:
  - bug
  - type-inference
  - multi-file
dependencies:
  - TASK-004
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Deferred overloads (e.g. `+` in `a: b: a + b`) don't survive the OutputTy boundary between files. When file A imports file B that exports an overloaded function, the overload context is lost — the exported type has free type vars instead of concrete types (shows as `? -> ? -> ?`).

A fix would require either carrying overload metadata in OutputTy or resolving all overloads before export. This erodes trust in the type system quickly for multi-file codebases.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Overloaded operators in exported functions retain their type constraints across file boundaries
- [ ] #2 Importing a file with `add = a: b: a + b` does not degrade to free type variables
- [ ] #3 Add regression test for cross-file overload preservation
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
