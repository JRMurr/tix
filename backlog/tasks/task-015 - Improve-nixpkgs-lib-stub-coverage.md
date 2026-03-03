---
id: TASK-015
title: Improve nixpkgs lib stub coverage
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
labels:
  - feature
  - stubs
  - dx
dependencies: []
references:
  - scripts/gen_lib_stubs.py
  - stubs/lib.tix
  - TODO/Tasks.md
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
~200 nixpkgs lib functions lack noogle signatures and are omitted from generated stubs. Users hitting unstubbed lib functions get top-type with no explanation.

`scripts/gen_lib_stubs.py` has been substantially improved (manual overrides for lists, attrsets, strings, options, modules, types) but gaps remain. Could supplement with `nix eval` + `functionArgs` for parameter names.

Also consider adding a diagnostic when a stub lookup returns top-type for a known lib path, so users understand why they're getting unhelpful types.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Identify and add stubs for the most commonly used lib functions still missing
- [ ] #2 Manual overrides added in scripts/gen_lib_stubs.py for identified functions
- [ ] #3 Consider diagnostic for known lib paths that resolve to top-type
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
