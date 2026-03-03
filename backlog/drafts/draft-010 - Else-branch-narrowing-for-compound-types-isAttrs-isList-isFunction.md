---
id: DRAFT-010
title: Else-branch narrowing for compound types (isAttrs/isList/isFunction)
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - feature
  - narrowing
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Currently `isAttrs`, `isList`, `isFunction` guards only narrow the then-branch because there's no `¬{..}` / `¬[..]` / `¬(→)` representation. The else-branch sees the original unconstrained type.

Needs design: should negation of structural types be added to the type algebra? Or is there a simpler approach for these specific guards?
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
