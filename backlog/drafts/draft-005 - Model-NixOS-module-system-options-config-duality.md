---
id: DRAFT-005
title: Model NixOS module system (options/config duality)
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
`mkOption`, `mkEnableOption`, `types.submodule`, `types.attrsOf` etc. are not modeled as first-class constructs. The stubs approximate it, but the `options.foo.enable` → `config.foo.enable` duality isn't captured.

- Enum option types degrade to `string` (no literal/singleton types)
- This is arguably the most important typing relationship in NixOS — the one between option declarations and option definitions

Requires design work: how to represent the module system's evaluation model in the type system, interaction with literal types (DRAFT-002), and what level of fidelity is practical.
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
