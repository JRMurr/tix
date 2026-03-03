---
id: TASK-013
title: Reduce allocations in hot-path constraint propagation
status: To Do
assignee: []
created_date: '2026-03-03 02:44'
labels:
  - performance
  - type-inference
dependencies: []
references:
  - 'crates/lang_check/src/constrain.rs:127-131'
  - 'crates/lsp/src/state.rs:595'
  - 'crates/lsp/src/state.rs:673'
  - 'crates/lang_check/src/infer_expr.rs:90'
  - 'crates/lang_ast/src/lib.rs:484-489'
  - 'TODO/code_review.md (items #16-19)'
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Several hot paths in type inference allocate unnecessarily:

1. **Bounds cloned on every constraint propagation** (`constrain.rs:127-131`): Full `Vec<TyId>` cloned to avoid borrow conflicts. Index-based iteration would avoid this allocation in the hottest function.
2. **TypeAliasRegistry cloned twice per file analysis** (`lsp/src/state.rs:595,673`): `Arc<TypeAliasRegistry>` would make this free.
3. **Full Expr clone on every infer_expr_inner call** (`infer_expr.rs:90`): Entire Expr enum cloned due to borrow checker constraints. Could match on `&Expr` and collect needed data into local Copy variables.
4. **Bindings::get() is O(n) linear scan** (`lang_ast/src/lib.rs:484-489`): Already marked with a FIXME. Called per attribute access during type inference.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Bounds propagation in constrain() uses index-based iteration instead of Vec clone
- [ ] #2 TypeAliasRegistry wrapped in Arc to eliminate clones in LSP state updates
- [ ] #3 infer_expr_inner avoids full Expr clone where possible
- [ ] #4 Bindings::get() uses a more efficient lookup (HashMap or similar)
- [ ] #5 No regressions in type inference correctness
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
