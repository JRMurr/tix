---
id: TASK-026
title: 'PBT: add correctness tests for structural union types'
status: To Do
assignee: []
created_date: '2026-03-08 21:31'
labels:
  - pbt
  - test-coverage
  - union-types
dependencies: []
references:
  - 'crates/lang_check/src/pbt/mod.rs:560-625'
  - 'crates/lang_check/src/pbt/mod.rs:539-541'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The focused union PBT tests (`test_union_prim_if_else`, `test_union_three_way`) only verify **primitive** unions (e.g. `int | string`). There are no correctness tests for unions containing structural types like `[int] | string`, `{a: int} | null`, or `(int -> int) | bool`.

Meanwhile, `test_combined_typing` silently skips correctness for any type containing unions (line 539-541) — it only checks crash freedom. This means structural unions have **zero exactness coverage**.

Add focused PBT generators and tests for:
- List unions: `[int] | string`, `[bool] | null`
- Attrset unions: `{a: int} | null`, `{a: int} | {b: string}`  
- Lambda unions: `(int -> int) | string`
- Mixed-depth unions: `[{a: int}] | string`

These should use the same direct if-then-else pattern as `arb_union_prim_if_else` (no let-binding wrapping) to avoid the early-canonicalization loss bug.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 PBT correctness test for 2-member unions where at least one member is a structural type (list, attrset, or lambda)
- [ ] #2 PBT correctness test for 2-member unions with both members being different structural types
- [ ] #3 Tests assert exact type match (not just crash freedom)
- [ ] #4 All new tests pass at 256+ cases
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
