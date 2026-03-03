---
id: TASK-017
title: Deduplicate shared code across crates
status: To Do
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-03 02:58'
labels:
  - tech-debt
  - code-quality
dependencies:
  - TASK-001
references:
  - crates/comment_parser/src/collect.rs
  - crates/comment_parser/src/tix_collect.rs
  - 'crates/lsp/src/state.rs:382-421'
  - 'crates/lsp/src/state.rs:632-664'
  - 'crates/lsp/src/completion.rs:789-872'
  - 'crates/lang_check/src/constrain.rs:579-609'
  - 'crates/lang_check/src/collect.rs:788-823'
  - 'TODO/code_review.md (items #20-23)'
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Four areas of significant code duplication identified in code review:

1. **Type expression collection** (`comment_parser/src/collect.rs` vs `tix_collect.rs`): `collect_type_expr`, `collect_union`, `collect_intersection`, `collect_attrset` are structurally identical. Acknowledged by COUPLING NOTICE comments. Bugs fixed in one might not be fixed in the other.
2. **Import resolution logic** (`lsp/src/state.rs:382-421` vs `632-664`): `update_file_inner` and `update_syntax_phase_b` have ~40 lines of identical import resolution.
3. **collect_visible_names and _no_inference** (`lsp/src/completion.rs:789-872`): Nearly identical functions differing only in whether `inference` is `Option` or required.
4. **ConstructorShape projection** (`constrain.rs:579-609` vs `collect.rs:788-823`): `are_types_disjoint` and `are_output_types_disjoint` do the same thing for different type representations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Type expression collection code shared between collect.rs and tix_collect.rs (or extracted to common module)
- [ ] #2 Import resolution logic deduplicated in LSP state
- [ ] #3 collect_visible_names variants unified
- [ ] #4 ConstructorShape projection made generic or shared
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
