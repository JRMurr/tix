---
id: TASK-021
title: 'PBT: generate union/intersection types and expand OutputTy Arbitrary'
status: Done
assignee: []
created_date: '2026-03-03 02:45'
updated_date: '2026-03-08 21:17'
labels:
  - test-coverage
  - pbt
  - type-inference
milestone: m-0
dependencies:
  - TASK-001
references:
  - 'crates/lang_check/src/pbt/mod.rs:219'
  - 'crates/lang_ty/src/arbitrary.rs:15-38'
  - 'TODO/code_review.md (items #29, #30)'
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Two related gaps in property-based testing:

1. **PBT doesn't generate union/intersection types** (`lang_check/src/pbt/mod.rs:219`): A core feature of the type system is absent from property-based testing. Acknowledged with a TODO.
2. **OutputTy Arbitrary impl missing variants** (`lang_ty/src/arbitrary.rs:15-38`): The simplification PBT never exercises `TyVar`, `Neg`, `Named`, `Top`, `Bottom` variants.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 PBT generates union types in arbitrary ASTs
- [ ] #2 PBT generates intersection types in arbitrary ASTs
- [ ] #3 OutputTy Arbitrary impl covers TyVar, Neg, Named, Top, and Bottom variants
- [ ] #4 Existing PBT properties still hold with expanded type generation
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
## Implementation Plan

### Background

The current PBT generates `(OutputTy, NixText)` pairs and asserts the type checker infers the expected type. Union/intersection types are explicitly excluded with a TODO. The `OutputTy` Arbitrary impl also omits TyVar, Neg, Named, Top, Bottom.

Key insight: union types arise naturally from **if-then-else with different-typed branches**, and intersection types arise in **negative position** (lambda parameters constrained from multiple sites) or from **narrowing with `&&`-combined guards**.

### Phase 1: Expand `OutputTy` Arbitrary impl (AC #3)

**File**: `crates/lang_ty/src/arbitrary.rs`

Add variants to `arb_arc_ty()`:
- **TyVar**: leaf variant, generate small `u32` (1..=8) — useful for testing type display, normalization, `free_type_vars()`, etc.
- **Neg**: wrap a primitive leaf in `Neg(TyRef)` — negation is only valid on atoms per the BAS design.
- **Named**: wrap any recursive inner type in `Named(SmolStr, TyRef)` with a generated alias name. Use `arb_smol_str_ident()` but with a capitalized prefix (e.g. `_Pbt_Alias...`) to look like real alias names.
- **Top / Bottom**: leaf variants, low weight.

Keep these new variants at low weight in `prop_oneof!` so they don't dominate. Existing code that calls `any::<OutputTy>()` and filters with `contains_union_or_intersection` / `has_non_primitive_lambda_param` will naturally filter out problematic combinations.

Add a standalone roundtrip property test: generate arbitrary `OutputTy` (with new variants), call `normalize_vars()`, verify it doesn't panic and is idempotent (`normalize_vars(normalize_vars(x)) == normalize_vars(x)`).

### Phase 2: Union type Nix code generation (AC #1)

**File**: `crates/lang_check/src/pbt/mod.rs`

#### Step 2a: `arb_union_if_else()` — simple union via if-then-else

Generate `if <bool-expr> then <A-expr> else <B-expr>` where A and B are **distinct** primitive types. The expected type is `OutputTy::Union([A, B])`.

```
Strategy:
  1. Pick two distinct PrimitiveTy values (filter A ≠ B)
  2. Generate Nix text for each via prim_ty_to_string
  3. Combine: "if true then ({a_text}) else ({b_text})"
  4. Expected type: Union of the two primitives (sorted to match canonicalization order)
```

Important: the union members must be sorted/normalized to match what the collector produces. Use `OutputTy::Union(vec![...]).normalize_vars()` to get canonical form, or sort by the same ordering the collector uses.

Wrap with `non_type_modifying_transform` for let-bind / attrset-select coverage.

#### Step 2b: `arb_union_nested()` — unions with structural types

Generate if-then-else where one branch is a list and the other a primitive, or one is an attrset and the other a primitive:
- `if true then [1] else "hello"` → `[int] | string`
- `if true then { x = 1; } else null` → `{ x: int } | null`

#### Step 2c: `arb_union_three_way()` — nested if for 3-member unions

```nix
if true then 1 else if true then "hello" else null
```
→ `int | string | null` (union gets flattened by collector)

#### Step 2d: Property test

New proptest block: `test_union_typing` — assert inferred type equals expected union (after normalization). ~256 cases combining 2a-2c strategies.

Also add a crash-freedom test with `arb_combined`-like weighting that includes union generators.

### Phase 3: Intersection type Nix code generation (AC #2)

Intersection types appear in two contexts:

#### Step 3a: Negative position — lambda param used with multiple constraints

Generate lambdas where the parameter is used in multiple type-incompatible ways, causing intersection in the inferred param type:

```nix
x: { a = x.name; b = x.value; }
```
→ `{ name: α, value: β, ... } -> { a: α, b: β }` — the param type is an open attrset (not intersection)

Better approach — use **narrowing with `&&`-combined `? field` guards** which produces intersection in the then-branch:

```nix
x: if x ? name && x ? value then x else {}
```
→ then-branch `x` has type `{name: α} & {value: β}` which merges to `{name: α, value: β}` for attrsets.

For true structural intersection (non-mergeable), we need different type constructors in `&&` guards. This is hard to produce naturally.

**Pragmatic approach**: Focus on what the type system actually produces as intersection in output:

1. **Crash-freedom with intersection inputs**: Generate `OutputTy::Intersection(...)` via the expanded Arbitrary (Phase 1) and test that `normalize_vars()`, `display()`, and `free_type_vars()` all handle it.

2. **Narrowing-based intersection**: Generate patterns like:
   ```nix
   x: if builtins.isString x then (if builtins.isInt x then x else 0) else 0
   ```
   The inner then-branch narrows x to `string & int` which should resolve to `Bottom` (or `never`). This tests the intersection/disjointness detection in constrain.

3. **Has-field conjunction**: Generate `x ? a && x ? b && x ? c` patterns and verify the then-branch x gets all fields. Expected type: open attrset with all named fields.

#### Step 3b: Property tests

- `test_intersection_narrowing_crash_freedom`: random `&&`-combined predicates (reuse `arb_guard_condition()` which already generates these, but specifically target `&&` combinations).
- `test_hasfield_conjunction_typing`: `x: if x ? a && x ? b then x.a + x.b else 0` → should infer `int` (both fields accessed, `+` constrains to int). Verify exact type.

### Phase 4: Integration into existing strategies (AC #4)

- Add union/intersection generators to `arb_combined()` with appropriate weights (e.g., 2 weight for union, 1 for intersection alongside existing 9:1 split).
- Run full test suite to verify no regressions.
- Update the header comment in `pbt/mod.rs` (lines 8-17) to remove the "no union/intersection coverage" limitation note.
- Update `arb_nix_text_from_ty()`: relax the `contains_union_or_intersection` filter for 2-member unions of primitives (since we can now generate code for those). Keep filtering complex unions/intersections.

### Ordering

1. Phase 1 first (pure type-level, no inference changes)
2. Phase 2 next (union codegen — straightforward if-then-else)
3. Phase 3 (intersection — builds on narrowing infrastructure)
4. Phase 4 last (integration + cleanup)

### Risks

- **Union normalization order**: The collector may sort union members differently than naive construction. Need to compare against `normalize_vars()` output or use the same canonical ordering.
- **Intersection in positive position is rare**: Most "intersection" in practice is attrset merging, which the collector simplifies to a single attrset. True structural intersection (`int & string` → Bottom) is what we'll mainly test. This is still valuable — it exercises the disjointness detection.
- **TASK-001 (recursive narrowing)**: Listed as a dependency but it's a draft/low-priority architecture issue. Union/intersection PBT generation doesn't depend on it — we're generating non-recursive code. Removing the dependency.
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
## Summary

Implemented union/intersection PBT coverage and expanded `OutputTy` Arbitrary, addressing the documented limitation of zero union/intersection coverage in the PBT suite.

### Changes

**Phase 1: OutputTy Arbitrary expansion** (`lang_ty/src/arbitrary.rs`)
- Added `TyVar`, `Top`, `Bottom`, `Neg`, `Named` variants at low weight to `arb_arc_ty`
- Added `normalize_vars` idempotency PBT in `arc_ty.rs`

**Phase 2: Union generation** (`lang_check/src/pbt/mod.rs`)
- Extended `text_from_ty()` to handle `OutputTy::Union` via nested if-then-else generation
- Added `union_strat` branch to `arb_nix_text`'s `prop_recursive` for recursive union generation
- Added focused `arb_union_prim_if_else` (2-member) and `arb_union_three_way` (3-member) strategies with exact type assertion
- Updated `arb_nix_text_from_ty` filter: allows unions, filters intersections/Neg/Top/Bottom/bare TyVar/Named
- Updated `arb_combined` with 7:1:1:1 weighting including focused union generators
- Added `normalize_set_ops()` helper for order/dedup-insensitive union comparison with nested flattening

**Phase 3: Intersection crash-freedom** (`lang_check/src/pbt/mod.rs`)
- `arb_intersection_param`: `||` narrowing producing `~pred1 & ~pred2`
- `arb_hasfield_conjunction`: `x ? a && x ? b` then field access, asserting return type is `int`
- `arb_intersection_contradiction`: contradictory narrowing (`isString && isInt`) crash freedom

**Phase 4: Integration**
- Added `arb_if_union_expr` to LSP PBT (`lsp/src/pbt.rs`) for union crash freedom
- Added `contains_intersection`, `contains_neg`, `contains_top_or_bottom`, `contains_bare_tyvar`, `contains_named` helpers to `OutputTy`
- Fixed `simplify` idempotency bug: flatten nested unions/intersections in `apply_simplification`, iterate to fixed point
- Updated header comments documenting coverage

### Known limitation discovered
Let-binding a union-typed expression loses the union through early canonicalization (reference sees only partial bounds). Documented in SESSION.md. Worked around in PBT by skipping `non_type_modifying_transform` for union types.

### Test results
- 1050 tests pass (all existing + 5 new PBT tests)
- 50k case PBT run passes
- clippy + fmt clean
<!-- SECTION:FINAL_SUMMARY:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
