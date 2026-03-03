---
id: DRAFT-008
title: Parameterized type aliases in .tix files
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - feature
  - stubs
dependencies: []
references:
  - SESSION.md
  - comment_parser/src/tix_decl.pest
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`type Overridable<T> = T | T -> T` would reduce duplication in stubs. Currently type aliases can't take parameters.

Requires grammar changes (`tix_decl.pest`), a `TypeApplication` ParsedTy variant, substitution engine, and arity checking. Useful for stubs but not critical — workaround is manual expansion.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
