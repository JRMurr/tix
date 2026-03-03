---
id: TASK-001
title: Union constraint snapshot/rollback for correct union subtyping
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
updated_date: '2026-03-03 03:00'
labels:
  - bug
  - type-inference
  - correctness
milestone: m-0
dependencies: []
references:
  - 'crates/lang_check/src/constrain.rs:474'
  - 'crates/lang_check/src/constrain.rs:488-494'
  - crates/lang_check/src/storage.rs
  - TODO/Tasks.md
  - 'TODO/code_review.md (items #1 and #10)'
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Union constraint routing in `constrain.rs` over-constrains when multiple paths exist. When `sub <: Union(a, b)` and neither member is disjoint or discriminant-matched, `sub` is constrained against **both** members. For example, an open attrset flowing into `Union({name:string}, {age:int})` is forced to have both fields.

Correct implementation needs state snapshots to try each union branch independently: try each branch with a snapshot, if one succeeds commit it, if all fail report the error.

This is a correctness fix — causes false positives on real code.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Implement snapshot/rollback for TypeStorage bounds
- [ ] #2 When constraining against a union, try each branch independently with snapshots
- [ ] #3 If one branch succeeds, commit it; if all fail, report the error
- [ ] #4 Add regression tests for union subtyping with multiple concrete members
- [ ] #5 No regressions in existing test suite
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
