---
id: DRAFT-011
title: Co-occurrence simplification (SimpleSub §4.2)
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - type-inference
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Current canonicalization could be relaxed to "occurrence signature" grouping per SimpleSub paper §4.2. This would produce simpler output types by grouping co-occurring type variables.

Research/design task — need to evaluate the trade-offs and determine if the current approach causes problems in practice.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
