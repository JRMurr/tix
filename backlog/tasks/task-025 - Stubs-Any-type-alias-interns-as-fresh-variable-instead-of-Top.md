---
id: TASK-025
title: 'Stubs: Any type alias interns as fresh variable instead of Top'
status: To Do
assignee: []
created_date: '2026-03-03 02:46'
labels:
  - bug
  - stubs
  - display
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`Any` is interned as a fresh unconstrained type variable (`new_var()`) rather than `OutputTy::Top`. Displays as a bare type variable (`a`) instead of `any`. Adding `Ty::Top` to the inference-time representation would fix this but requires updates to `constrain.rs`. Low priority — correct inference behavior, just incorrect display.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Any type alias resolves to Top, not a fresh type variable
- [ ] #2 Display shows 'any' instead of a bare type variable letter
- [ ] #3 Constraint propagation correctly handles Top in all positions
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
