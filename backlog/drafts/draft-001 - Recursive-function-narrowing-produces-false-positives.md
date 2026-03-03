---
id: DRAFT-001
title: Recursive function narrowing produces false positives
status: Draft
assignee: []
created_date: '2026-03-03 02:46'
labels:
  - bug
  - narrowing
  - architecture
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Recursive functions with `isFunction`/`isAttrs`/`isList` narrowing on the same parameter produce false positives. Root cause: SCC-level inference shares a single type variable for the parameter across all call sites, including recursive calls from other branches.

Fix requires per-call-site flow sensitivity, which is beyond the current SCC architecture. This affects real nixpkgs code (modules.nix, generators.nix).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Recursive functions with type-guard narrowing on the same parameter don't produce false positive errors
- [ ] #2 modules.nix and generators.nix patterns type-check without errors
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
