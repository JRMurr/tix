---
id: DRAFT-012
title: Intersection-type-based operator overloading
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - type-inference
  - architecture
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The current deferred overload approach adds significant complexity to extrusion (fixed-point loop for re-instantiation, interaction with constraint cache). An alternative is intersection-type-based overloading which would be more principled.

For example, `+` could be typed as `(int -> int -> int) & (string -> string -> string) & (float -> float -> float)` instead of using deferred resolution.

Needs design: interaction with the existing constraint system, performance implications, and whether it fully replaces or supplements deferred overloads.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
