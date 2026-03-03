---
id: TASK-005
title: Fix chained || null guard narrowing error
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
labels:
  - bug
  - narrowing
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`a == null || b == null || c == null` produces a `~null` vs `null` error in the rightmost operand. Left-associative `||` applies else-branch narrowing from the compound LHS to the RHS. Most `||` patterns work, but chained null guards on 3+ variables surface this issue.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Chained null guards (3+ variables) with || do not produce false positive errors
- [ ] #2 Existing || narrowing behavior preserved for 2-variable cases
- [ ] #3 Add regression test for a == null || b == null || c == null
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
