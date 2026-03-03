---
id: TASK-018
title: Fix inverted lang_ty → lang_ast dependency
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
labels:
  - tech-debt
  - architecture
dependencies: []
references:
  - 'TODO/code_review.md (item #26)'
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`lang_ty` (lower-level type representation) depends on `lang_ast` (higher-level AST/parsing) only for 2 `From` impls. This inverts the natural dependency direction. The `From` impls could live elsewhere (e.g., in `lang_check` or as standalone conversion functions).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 lang_ty no longer depends on lang_ast
- [ ] #2 From impls moved to an appropriate location (lang_check or similar)
- [ ] #3 Build and tests pass with corrected dependency direction
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
