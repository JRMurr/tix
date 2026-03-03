---
id: TASK-014
title: Make narrowing guard list extensible via stubs
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
labels:
  - feature
  - narrowing
  - stubs
dependencies: []
references:
  - 'crates/lang_ast/src/narrow.rs:89'
  - comment_parser/src/tix_decl.pest
  - comment_parser/src/tix_collect.rs
  - docs/src/stubs.md
  - TODO/Tasks.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Type narrowing guards in `narrow.rs:89` are hardcoded. Third-party libraries can't declare their own type guards. There's a TODO in the code describing the approach.

Proposed approach:
1. Add an `@inline` annotation in `.tix` stub syntax
2. When loading stubs, register annotated functions as narrowing guards
3. Update `analyze_condition` to check the registry in addition to hardcoded builtins
4. Update `.tix` syntax documentation in the mdbook
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 New @inline annotation supported in .tix stub syntax
- [ ] #2 Stubs with @inline annotations register functions as narrowing guards
- [ ] #3 analyze_condition checks stub-registered guards in addition to hardcoded builtins
- [ ] #4 Documentation updated in docs/src/ for new .tix annotation
- [ ] #5 Add test for custom narrowing guard defined in stubs
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
