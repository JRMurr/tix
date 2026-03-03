---
id: TASK-010
title: 'LSP: Hover on multi-element attrpaths shows wrong type'
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
updated_date: '2026-03-03 03:03'
labels:
  - bug
  - lsp
  - hover
milestone: m-0
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
rnix parses `a.foo.bar` as a single Select with a two-element attrpath, not nested Selects. Hovering on any element shows the overall result type rather than the intermediate type. Fixing requires mapping individual attrpath elements back to their corresponding intermediate ExprIds from the Tix AST lowering (which does produce nested Selects).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Hovering on 'foo' in a.foo.bar shows the type of a.foo (intermediate), not a.foo.bar
- [ ] #2 Hovering on 'bar' still shows the full result type of a.foo.bar
- [ ] #3 Add E2E test for hover on multi-segment attrpaths
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
