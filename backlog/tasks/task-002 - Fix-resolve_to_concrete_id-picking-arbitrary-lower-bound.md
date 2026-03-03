---
id: TASK-002
title: Fix resolve_to_concrete_id picking arbitrary lower bound
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
labels:
  - bug
  - type-inference
  - correctness
dependencies: []
references:
  - 'crates/lang_check/src/type_table.rs:161-181'
  - 'crates/lang_check/src/infer.rs:271-276'
  - 'TODO/code_review.md (item #5)'
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`resolve_to_concrete_id_inner` in `type_table.rs:161-181` returns the **first** concrete bound found, regardless of how many exist. A variable with `[Int, String]` lower bounds resolves to `Int`, silently losing `String`. The intent (per comment at `infer.rs:271-276`) is to only resolve when there's a single concrete lower bound.

A previous fix enforcing single-bound semantics was reverted — it regressed the extrusion flow that depends on seeing through variables to find Lambda structure (`wrapper_foldl_int_and_list` test). Needs a more nuanced approach that accounts for poly_type_env / extrusion interaction.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 resolve_to_concrete_id returns None when multiple distinct concrete lower bounds exist
- [ ] #2 poly_type_env recording correctly handles the single-bound case
- [ ] #3 wrapper_foldl_int_and_list test still passes (extrusion Lambda lookup works)
- [ ] #4 Add regression test for variable with multiple concrete lower bounds
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
