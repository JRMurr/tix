---
id: TASK-021
title: 'PBT: generate union/intersection types and expand OutputTy Arbitrary'
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-03 02:58'
labels:
  - test-coverage
  - pbt
  - type-inference
dependencies:
  - TASK-001
references:
  - 'crates/lang_check/src/pbt/mod.rs:219'
  - 'crates/lang_ty/src/arbitrary.rs:15-38'
  - 'TODO/code_review.md (items #29, #30)'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Two related gaps in property-based testing:

1. **PBT doesn't generate union/intersection types** (`lang_check/src/pbt/mod.rs:219`): A core feature of the type system is absent from property-based testing. Acknowledged with a TODO.
2. **OutputTy Arbitrary impl missing variants** (`lang_ty/src/arbitrary.rs:15-38`): The simplification PBT never exercises `TyVar`, `Neg`, `Named`, `Top`, `Bottom` variants.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 PBT generates union types in arbitrary ASTs
- [ ] #2 PBT generates intersection types in arbitrary ASTs
- [ ] #3 OutputTy Arbitrary impl covers TyVar, Neg, Named, Top, and Bottom variants
- [ ] #4 Existing PBT properties still hold with expanded type generation
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
