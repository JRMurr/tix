---
id: DRAFT-002
title: Intersection annotation body verification
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - type-inference
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Per-component verification of intersection-of-function annotations is deferred. Currently, `(int -> int) & (string -> string)` is accepted as a declared type (store-and-trust), but the body is not checked against each component separately.

Full verification would require either re-inferring the body once per component or adding a check-mode to the inference engine. Need to design the approach before implementation.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
