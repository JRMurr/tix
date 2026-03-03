---
id: DRAFT-006
title: Resolve angle-bracket imports (<nixpkgs>)
status: Draft
assignee: []
created_date: '2026-03-03 02:51'
labels:
  - needs-plan
  - feature
  - multi-file
dependencies: []
references:
  - SESSION.md
  - crates/lang_ast/src/imports.rs
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Angle bracket search paths (`<nixpkgs>`) are silently skipped during import resolution (TODOs in `imports.rs:69,148`). Users get silent `?` with no guidance on what to do instead. Common in older-style Nix code (`pkgs ? import <nixpkgs> {}`).

Needs NIX_PATH lookup to resolve properly. Design questions: should Tix read NIX_PATH from environment? From tix.toml config? Should it produce a diagnostic suggesting alternatives (flakes, stubs)?
<!-- SECTION:DESCRIPTION:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
