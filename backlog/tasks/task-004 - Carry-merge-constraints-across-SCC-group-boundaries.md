---
id: TASK-004
title: Carry merge constraints across SCC group boundaries
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
labels:
  - bug
  - type-inference
  - correctness
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Polymorphic `//` merge constraints are discarded at SCC group end (only overloads are carried). This means `let f = a: b: (a // b).z; in f { x = 1; } { y = 2; }` does NOT error — the merge never resolves because neither operand becomes concrete within the SCC group.

Fixing requires carrying merge constraints (similar to overloads) and re-instantiating them during extrusion.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Merge constraints survive SCC group boundaries like overload constraints do
- [ ] #2 Re-instantiation during extrusion handles carried merge constraints
- [ ] #3 f { x = 1; } { y = 2; } accessing .z produces an error
- [ ] #4 Add regression tests for cross-SCC merge constraint resolution
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
