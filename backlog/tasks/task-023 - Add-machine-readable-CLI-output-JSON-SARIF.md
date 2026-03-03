---
id: TASK-023
title: Add machine-readable CLI output (JSON/SARIF)
status: To Do
assignee: []
created_date: '2026-03-03 02:46'
updated_date: '2026-03-03 03:08'
labels:
  - feature
  - cli
  - dx
milestone: m-0
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
No machine-readable output format for CLI. Can't integrate with GitHub PR annotations or code review tools without parsing miette output. Need `--format json` and ideally SARIF support for CI integration.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 --format json flag produces structured JSON output with diagnostics
- [ ] #2 JSON output includes file path, line/column, severity, message for each diagnostic
- [ ] #3 Consider SARIF format for GitHub integration
- [ ] #4 Documentation updated for new CLI flag
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
