---
id: TASK-016
title: 'Stub generator: fix tryEval failures and namespace doc comments'
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-03 03:05'
labels:
  - feature
  - stubs
  - dx
milestone: m-0
dependencies: []
references:
  - SESSION.md
  - tools/extract-options.nix
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Two issues with the stub generators (nixos.tix / home-manager.tix):

1. **tryEval failures silently degrade types** — affects common options like `networking.firewall.allowedTCPPorts` (should be `[int]`), `boot.kernelParams` (should be `[string]`), and 593 `enable` fields. Types degrade to `{ ... }`.
2. **No namespace-level doc comments** — generated stubs only have `##` doc comments on leaf options, not on intermediate namespace fields. Completing `programs.` shows no docs for most entries. Could hoist `enable` descriptions up to the parent namespace.
3. **92 redundant `{ ... } | { ... }` unions** should be deduplicated.
4. **`specialisation` embeds ~90k lines** of recursive NixOS config inline instead of referencing `NixosConfig`.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 tryEval failures produce correct types for common options (allowedTCPPorts as [int], etc.)
- [ ] #2 Intermediate namespace fields have doc comments (e.g. programs. shows descriptions)
- [ ] #3 Redundant { ... } | { ... } unions are deduplicated
- [ ] #4 specialisation references NixosConfig instead of inlining
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
