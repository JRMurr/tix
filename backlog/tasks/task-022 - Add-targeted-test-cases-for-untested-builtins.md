---
id: TASK-022
title: Add targeted test cases for untested builtins
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
labels:
  - test-coverage
  - builtins
dependencies: []
references:
  - 'TODO/code_review.md (items #31, #33, #34)'
  - 'crates/lsp/tests/e2e_nixpkgs.rs:111'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Many builtins lack dedicated type inference test cases: `fromJSON`, `split`, `match`, `replaceStrings`, `sort`, `partition`, `groupBy`, `mapAttrs`, `functionArgs`, `listToAttrs`, `removeAttrs`, `genList`, `concatLists`, `concatMap`, `all`, `any`, and others.

Also: path interpolation (`./dir/${name}/file.nix`) has zero test coverage, and `nixpkgs_lib_no_crash` test is fully commented out at `lsp/tests/e2e_nixpkgs.rs:111` (disabled outside the normal `#[ignore]` mechanism).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Type inference tests for fromJSON, split, match, replaceStrings
- [ ] #2 Type inference tests for sort, partition, groupBy, mapAttrs
- [ ] #3 Type inference tests for functionArgs, listToAttrs, removeAttrs, genList, concatLists, concatMap, all, any
- [ ] #4 Test case for path interpolation (./dir/${name}/file.nix)
- [ ] #5 nixpkgs_lib_no_crash test either re-enabled with #[ignore] or removed
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
