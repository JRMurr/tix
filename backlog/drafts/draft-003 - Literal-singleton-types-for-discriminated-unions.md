---
id: DRAFT-003
title: Literal / singleton types for discriminated unions
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - type-inference
  - feature
dependencies: []
references:
  - SESSION.md
  - docs/src/limitations.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`"circle"` is `string`, not `"circle"`. No TypeScript-style discriminated unions.

Impact across multiple personas:
- NixOS enum options become `string`
- String-keyed dispatch (`if name == "gcc"`) can't narrow
- Tagged union idioms common in nixpkgs can't be expressed

Documented in limitations.md. Requires type system extension — new type constructors, constraint rules, and integration with narrowing.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
