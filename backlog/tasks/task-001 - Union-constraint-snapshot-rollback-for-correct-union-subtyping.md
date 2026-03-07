---
id: TASK-001
title: Union constraint snapshot/rollback for correct union subtyping
status: To Do
assignee: []
created_date: '2026-03-03 02:43'
updated_date: '2026-03-07 16:15'
labels:
  - type-inference
  - infrastructure
milestone: m-0
dependencies: []
references:
  - 'crates/lang_check/src/constrain.rs:474'
  - 'crates/lang_check/src/constrain.rs:488-494'
  - crates/lang_check/src/storage.rs
  - TODO/Tasks.md
  - 'TODO/code_review.md (items #1 and #10)'
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Union constraint routing in `constrain.rs:500-505` over-constrains when multiple paths exist. When `sub <: Union(a, b)` and both members are concrete but neither is disjoint from `sub` and the discriminant tiebreaker doesn't resolve, `sub` is constrained against **both** members.

**Key finding (2026-03-07):** This code path is currently **unreachable** because `intern_parsed_ty` represents union annotations as variables with lower bounds, not as concrete `Ty::Union(a, b)`. Confirmed via instrumentation — zero hits across the entire test suite including PBT. The concrete `Ty::Union` on RHS only appears from De Morgan normalization (Neg members), `constrain_lhs_inter` variable isolation (Union(sup, neg_c)), and extrusion of those — none of which produce `Union(AttrSet, AttrSet)`.

This becomes relevant if/when `intern_parsed_ty` is changed to create concrete `Ty::Union` instead of variables (which would give more precise union routing). Until then, this is defensive infrastructure.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Implement snapshot/rollback for TypeStorage bounds
- [ ] #2 When constraining against a union, try each branch independently with snapshots
- [ ] #3 If one branch succeeds, commit it; if all fail, report the error
- [ ] #4 Add regression tests for union subtyping with multiple concrete members
- [ ] #5 No regressions in existing test suite
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
## Approach: Clone-Before + Watermarks

Hybrid strategy for snapshotting constraint solver state:

### Step 1: Extract `ConstraintCaches` struct in `type_table.rs`

Group the 4 snapshotted caches into a single `#[derive(Clone)]` struct:

```rust
#[derive(Debug, Clone)]
pub(crate) struct ConstraintCaches {
    pub(crate) constrain_cache: FxHashSet<(TyId, TyId)>,
    pub(crate) neg_cache: FxHashMap<TyId, TyId>,
    pub(crate) inter_var_cache: FxHashMap<TyId, bool>,
    pub(crate) union_member_cache: FxHashSet<(TyId, TyId)>,
}
```

Update `TypeTable` to hold `caches: ConstraintCaches`. Update ~8 call sites from `self.types.constrain_cache` → `self.types.caches.constrain_cache` (in `constrain.rs` + `infer.rs`).

### Step 2: Add `Snapshot` struct and rollback helpers

```rust
pub(crate) struct Snapshot {
    entries_watermark: usize,
    bounds_modifications: FxHashMap<TyId, (usize, usize)>,
    caches: ConstraintCaches,
}
```

Rollback strategies per state:
- **`storage.entries`**: Watermark — save len, truncate on rollback
- **Variable bounds** (`lower_bounds`/`upper_bounds`): Track modified vars + pre-speculation lengths via `FxHashMap<TyId, (usize, usize)>`, truncate each on rollback
- **Caches**: Clone `ConstraintCaches` before, swap back on rollback

Add `active_snapshot: Option<Box<Snapshot>>` to `TypeTable` with `snapshot()`, `rollback()`, `commit()` methods.

Add bound-recording wrappers (`add_lower_bound`, `add_upper_bound`) on TypeTable that record pre-speculation lengths in the active snapshot before delegating to storage.

### Step 3: Update call sites in `constrain.rs`

Change the 2 bound-mutation calls to use TypeTable wrappers:
- Line ~120: `self.types.storage.add_upper_bound(sub, sup)` → `self.types.add_upper_bound(sub, sup)`
- Line ~140: `self.types.storage.add_lower_bound(sup, sub)` → `self.types.add_lower_bound(sup, sub)`

### Step 4: Add `speculative_union_constrain`

Replace lines 500-505 (the over-constraining fallback) with:

```rust
fn speculative_union_constrain(&mut self, sub_id: TyId, a: TyId, b: TyId) -> Result<(), InferenceError> {
    let saved_expr = self.current_expr;
    self.types.snapshot();
    match self.constrain(sub_id, a) {
        Ok(()) => { self.types.commit(); return Ok(()); }
        Err(_) => { self.types.rollback(); self.current_expr = saved_expr; }
    }
    self.constrain(sub_id, b)
}
```

### Step 5: Prerequisite — change `intern_parsed_ty` for Union

The speculative path is currently unreachable because `intern_parsed_ty` creates variables for unions. To make this feature useful, change 2-member unions to create concrete `Ty::Union(a, b)` instead. This is the trigger that makes the snapshot/rollback infrastructure necessary.

### Key files
- `crates/lang_check/src/type_table.rs` — ConstraintCaches, Snapshot, snapshot/rollback/commit
- `crates/lang_check/src/storage.rs` — `truncate_entries()`, `get_var_mut()`
- `crates/lang_check/src/constrain.rs` — 2 bound call sites, `speculative_union_constrain`
- `crates/lang_check/src/lib.rs` — `intern_parsed_ty` Union case (prerequisite change)

### Edge cases
- **Nesting**: Start with `debug_assert!` disallowing nested speculation. Upgrade to `Vec<Box<Snapshot>>` if needed.
- **Deadline during speculation**: `constrain()` returns `Ok(())` on timeout → branch "succeeds" and commits. Correct — partial inference is acceptable.
- **De Morgan in alloc_concrete**: Recursive allocations create entries + neg_cache inserts. Both covered by watermark + cache clone.
- **Bounds dedup**: Only first modification per variable recorded (captures "before" lengths).
<!-- SECTION:PLAN:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
