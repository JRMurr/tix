---
id: TASK-003
title: Null-default field loses polymorphic return type
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
labels:
  - bug
  - type-inference
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`let f = { config ? null }: config; in f {}` returns a free type variable instead of `null`. The canonical type displays as `{ config?: a } -> null` rather than `{ config?: a } -> (a | null)`. Likely an interaction between optional-field default handling and extrusion.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 f {} infers as null (the default value) when config is not provided
- [ ] #2 f { config = 42; } infers as int
- [ ] #3 Canonical display shows the union correctly: { config?: a } -> (a | null)
- [ ] #4 Add regression test for null-default field inference
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
