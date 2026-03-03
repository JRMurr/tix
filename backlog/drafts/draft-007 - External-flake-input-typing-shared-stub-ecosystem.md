---
id: DRAFT-007
title: External flake input typing / shared stub ecosystem
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - feature
  - ecosystem
dependencies: []
references:
  - SESSION.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
No stubs for third-party flake outputs. A NixOS config user has 30-50% of their config (community modules, hyprland, sops-nix, etc.) as `?`. There's no convention for flake authors to publish `.tix` stubs. No DefinitelyTyped equivalent, no `tix install-stubs`.

This is a chicken-and-egg ecosystem problem. Needs strategic design:
- Convention for publishing `.tix` with flakes
- Auto-discovery of stubs from flake inputs
- Central registry or per-flake approach
- Interaction with `tix.toml` context system
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
