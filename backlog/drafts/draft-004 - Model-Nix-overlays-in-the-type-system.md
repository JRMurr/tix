---
id: DRAFT-004
title: Model Nix overlays in the type system
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - feature
  - architecture
dependencies: []
references:
  - SESSION.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Overlays are the primary composition mechanism in real Nix codebases. Tix has no model for them.

- `final`/`prev` parameters are `?`. Overlay-injected packages don't appear in `Pkgs` type.
- No `@overlay` context equivalent to `@nixos`/`@callpackage`.
- `gen-stubs pkgs` only captures the base nixpkgs set, not overlay additions.
- For users whose architecture is overlay stacking, Tix types individual files but can't follow the overlay chain.

Needs design work to determine how overlays interact with the existing context/stub system.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
