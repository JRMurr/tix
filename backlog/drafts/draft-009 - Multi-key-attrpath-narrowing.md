---
id: DRAFT-009
title: Multi-key ? attrpath narrowing
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
  - crates/lang_ast/src/narrow.rs
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Only single-key `x ? field` narrowing is supported. Multi-segment attrpaths like `x ? foo.bar.baz` silently fail to narrow (`single_static_attrpath_key()` returns `None` for multi-segment paths).

Part of the broader narrowing enhancement set. Needs design for how nested field presence maps to type constraints.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
