---
id: TASK-027
title: 'PBT: reduce arb_nix_text_from_ty rejection rate'
status: To Do
assignee: []
created_date: '2026-03-08 21:32'
labels:
  - pbt
  - test-coverage
  - dx
dependencies: []
references:
  - 'crates/lang_check/src/pbt/mod.rs:418-432'
  - 'crates/lang_ty/src/arbitrary.rs:15-52'
  - 'crates/lang_check/src/pbt/mod.rs:522-524'
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The type-directed PBT generator `arb_nix_text_from_ty` filters out types containing intersections, negation, top/bottom, bare TyVars, Named wrappers, and non-primitive lambda params. With the default `OutputTy::Arbitrary` params (depth 4, desired_size 64), the majority of generated types hit at least one filter, leading to a very high rejection rate — evidenced by the 500,000 `max_local_rejects` tolerance in `test_combined_typing`.

This means the type-directed generator contributes very little actual coverage beyond what `arb_nix_text` already provides.

Options to explore:
1. **Reduce depth/size** for the OutputTy Arbitrary used by `arb_nix_text_from_ty` (e.g. depth 2, desired_size 16) — shallower types are less likely to contain filtered variants
2. **Build types constructively** — instead of generate-then-filter, build types from a grammar that only produces representable types (primitives, lists, attrsets, lambdas with primitive params, unions of representable types)
3. **Weight the OutputTy leaf generation** to suppress filtered variants — e.g. remove TyVar/Top/Bottom/Neg from the leaf distribution when used by PBT

Option 2 is likely the best long-term fix since it eliminates rejection entirely.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 arb_nix_text_from_ty generates a representable type on >50% of attempts (down from near-majority rejection)
- [ ] #2 max_local_rejects for test_combined_typing can be reduced to ≤50,000
- [ ] #3 No loss in type coverage — still exercises lists, attrsets, lambdas, unions
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
