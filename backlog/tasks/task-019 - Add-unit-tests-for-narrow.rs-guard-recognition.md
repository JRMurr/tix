---
id: TASK-019
title: Add unit tests for narrow.rs guard recognition
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
labels:
  - test-coverage
  - narrowing
dependencies: []
references:
  - crates/lang_ast/src/narrow.rs
  - 'TODO/code_review.md (items #27, #32)'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`crates/lang_ast/src/narrow.rs` (645 lines) has zero unit tests. Complex condition analysis is only tested indirectly through integration tests. Guard recognition, alias tracing, and the `MAX_ALIAS_TRACE_DEPTH` mechanism are untested in isolation.

Additionally, several existing narrowing tests have weak assertions — they only verify "doesn't crash" rather than checking inferred types (`narrow_hasfield_preserves_original_constraints`, `narrow_let_generalization_preserved`, `e2e_multi_file::multiple_files_independent`).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Unit tests for each guard type in analyze_condition (isNull, isString, isInt, etc.)
- [ ] #2 Unit tests for alias tracing and MAX_ALIAS_TRACE_DEPTH
- [ ] #3 Unit tests for boolean combinator narrowing (&&, ||, !)
- [ ] #4 Strengthen weak narrowing test assertions to check actual inferred types
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
