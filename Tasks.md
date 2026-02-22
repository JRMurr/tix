# Tix Refactoring Tasks

Architectural improvements identified via code review (Feb 2026). Each task is
scoped to a single session and is self-contained enough for an agent to pick up
with no prior context beyond this file and `CLAUDE.md`.

Tasks are grouped by theme. Within each group they're ordered by dependency
(earlier tasks make later ones easier but aren't strict prerequisites unless
noted). Effort/impact ratings are relative to each other.

---

## Theme A: Type System Representation

### ~~A1. Introduce `Polarity` enum to replace `bool`~~ ✅ Done

**Effort**: Low | **Impact**: Medium | **Risk reduction**: Prevents silent sign-flip bugs

Polarity is currently threaded as `bool` through `extrude`, `canonicalize`, and
`link_extruded_var`. A typo of `polarity` instead of `!polarity` silently
compiles.

**What to do**:

1. Add to `lang_check/src/lib.rs` (or a new `polarity.rs`):
   ```rust
   #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
   pub enum Polarity { Positive, Negative }
   impl Polarity {
       pub fn flip(self) -> Self {
           match self { Positive => Negative, Negative => Positive }
       }
       pub fn is_positive(self) -> bool { matches!(self, Positive) }
   }
   ```
2. Replace every `polarity: bool` parameter in:
   - `infer.rs`: `extrude`, `extrude_inner`, `link_extruded_var`
   - `collect.rs`: `Canonicalizer::canonicalize`, `canonicalize_inner`,
     `expand_bounds_as_union/intersection`, `canonicalize_concrete`,
     `canonicalize_standalone`
   - `collect.rs` `Collector::finalize_inference` (the `true` passed to
     `canonicalize`)
3. Replace `!polarity` with `polarity.flip()` everywhere.
4. Replace `if polarity { ... } else { ... }` with `match polarity { ... }`.
5. Update the `cache` key in `Canonicalizer` from `(TyId, bool)` to
   `(TyId, Polarity)`.
6. Run `cargo test` — all existing tests should pass unchanged.
7. Run `cargo clippy` to catch any leftover `bool` usage.

**Files touched**: `lang_check/src/infer.rs`, `lang_check/src/collect.rs`,
`lang_check/src/lib.rs`

**Regression test**: None needed (no behavioral change), but verify PBT still
passes (`./scripts/pbt.sh`).

---

### ~~A2. Add `OutputTy::Bottom` (Never) variant~~ ✅ Done

**Effort**: Medium | **Impact**: Medium | **Risk reduction**: Makes contradictions visible

Contradictions like `int & ~int` are currently collapsed to a bare `TyVar`
(`collect.rs:172-174`), making them invisible in diagnostics. An explicit
`Bottom`/`Never` type makes dead branches detectable.

**What to do**:

1. Add `Bottom` variant to `OutputTy` in `lang_ty/src/arc_ty.rs`.
2. Update `Display` impl: display as `never` (or `bottom`).
3. Update `for_each_child` and `map_children`: `Bottom` is a leaf (no children).
4. Update `free_type_vars`: `Bottom` has no free vars.
5. In `collect.rs`, `has_primitive_contradiction`: return `OutputTy::Bottom`
   instead of `OutputTy::TyVar(var_id.0)`.
6. In `expand_bounds_as_union`, if a member is `Bottom`, filter it out (bottom
   is identity for union).
7. In `expand_bounds_as_intersection`, if any member is `Bottom`, the whole
   intersection is `Bottom` (bottom is absorbing for intersection).
8. Update `lang_ty/src/simplify.rs` if it pattern-matches on `OutputTy`
   variants.
9. Update `arc_ty!` macro if desired (e.g. `arc_ty!(Bottom)`).
10. Add unit tests in `collect.rs::tests` for `Bottom` propagation through
    union/intersection.
11. Add a regression test in `lang_check/src/tests.rs` for a Nix expression
    that produces a contradiction, verifying the output contains `never`.

**Files touched**: `lang_ty/src/arc_ty.rs`, `lang_check/src/collect.rs`,
`lang_ty/src/simplify.rs`, `lang_check/src/tests.rs`

---

### A3. Add `OutputTy::Top` variant (stretch — do after A2)

**Effort**: Medium | **Impact**: Low-Medium

Tautologies like `null | ~null` are currently removed silently
(`remove_tautological_pairs`). If the tautology is the *only* member, the result
becomes an empty union which falls through to `TyVar`. An explicit `Top` would
be more honest. Lower priority than `Bottom` because tautologies are rarer.

---

## Theme B: CheckCtx Decomposition

### ~~B1. Extract `TypeTable` from `CheckCtx`~~ ✅ Done

**Effort**: Medium-High | **Impact**: High | **Risk reduction**: High — isolates
constraint state from inference orchestration

`CheckCtx` has 14 fields mixing type storage, constraint caches, inference
state, narrowing maps, and external declarations. Every `impl CheckCtx` method
can see everything. Extracting the core type table makes it independently
testable and prevents accidental cross-concern coupling.

**What to do**:

1. Create `lang_check/src/type_table.rs` containing:
   ```rust
   pub struct TypeTable {
       pub(crate) storage: TypeStorage,
       pub(crate) constrain_cache: HashSet<(TyId, TyId)>,
       pub(crate) prim_cache: HashMap<PrimitiveTy, TyId>,
   }
   ```
2. Move these methods from `CheckCtx` to `TypeTable`:
   - `new_var`, `alloc_concrete`, `alloc_prim` (from `lib.rs:394-419`)
   - `constrain`, `constrain_concrete`, `constrain_attrsets` (from `constrain.rs`)
   - `find_concrete`, `find_concrete_inner` (from `infer.rs:695-717`)
   - `resolve_to_concrete_id`, `resolve_to_concrete_id_inner` (from `infer.rs:667-692`)

   These methods only use `table`, `prim_cache`, and `constrain_cache` — no
   other CheckCtx fields. Except: `constrain` currently reads `self.expr_for_ty()`
   to update `current_expr`. That expr-attribution logic should stay in CheckCtx
   as a wrapper that calls `self.types.constrain(sub, sup)` and handles the
   expr-tracking itself.

3. Replace `self.table` / `self.prim_cache` / `self.constrain_cache` in
   `CheckCtx` with a single `types: TypeTable` field.
4. Update all call sites: `self.new_var()` → `self.types.new_var()`, etc. For
   `constrain`, keep a thin `CheckCtx::constrain` that does the
   `expr_for_ty` / `current_expr` attribution, then delegates to
   `self.types.constrain(sub, sup)`.
5. Run full test suite.

**Files touched**: New `lang_check/src/type_table.rs`, changes to
`lang_check/src/lib.rs`, `constrain.rs`, `infer.rs`, `infer_expr.rs`,
`collect.rs`, `builtins.rs`, `narrow.rs`

**Testing**: Write a few direct unit tests on `TypeTable` in isolation (create
vars, constrain them, verify bounds). This validates that constraint propagation
works independently of inference.

---

### ~~B2. Unify `find_concrete` and `resolve_to_concrete_id`~~ ✅ Done

**Effort**: Low | **Impact**: Low | **Risk reduction**: Eliminates code duplication

`infer.rs` has two nearly identical functions that walk lower bounds looking for
concrete types — `find_concrete` returns `Option<Ty<TyId>>` and
`resolve_to_concrete_id` returns `Option<TyId>`. They have the same traversal
and cycle-detection logic.

**What to do**:

1. Keep `resolve_to_concrete_id` as the single implementation (returns
   `Option<TyId>` — the strictly more informative return type).
2. Replace every `find_concrete(id)` call site with
   `resolve_to_concrete_id(id).map(|id| table.get(id).as_concrete().clone())`.
   Or add a convenience `find_concrete` that delegates to
   `resolve_to_concrete_id`:
   ```rust
   fn find_concrete(&self, ty_id: TyId) -> Option<Ty<TyId>> {
       let id = self.resolve_to_concrete_id(ty_id)?;
       match self.table.get(id) {
           TypeEntry::Concrete(ty) => Some(ty.clone()),
           _ => None,
       }
   }
   ```
3. Delete the old `find_concrete_inner`.
4. Run tests.

**Files touched**: `lang_check/src/infer.rs`

---

## Theme C: Narrowing Simplification

### ~~C1. Deduplicate `walk_for_narrow_scopes` binding iteration~~ ✅ Done

**Effort**: Low | **Impact**: Low-Medium | **Risk reduction**: Prevents
copy-paste divergence

`narrow.rs:570-632` has near-identical 30-line blocks for `LetIn` and
`AttrSet { is_rec: true }` — both iterate static bindings, record narrowings
per name, and recurse into child expressions. They differ only in whether
there's a `body` to recurse into.

**What to do**:

1. Extract a helper:
   ```rust
   fn record_and_walk_bindings(
       &self,
       bindings: &Bindings,
       active: &[NarrowBinding],
       scopes: &mut HashMap<NameId, Vec<NarrowBinding>>,
   ) { ... }
   ```
2. Both the `LetIn` and `AttrSet { is_rec: true }` arms call this helper. The
   `LetIn` arm additionally recurses into `body`.
3. Run tests.

**Files touched**: `lang_check/src/narrow.rs`

---

### ~~C2. Move narrowing scope detection into SCC grouping~~ ✅ Done

**Effort**: High | **Impact**: High | **Risk reduction**: Eliminates the
parallel AST walk

The `compute_binding_narrow_scopes` pre-pass (`narrow.rs:503-641`) walks the
entire AST to figure out which let-bindings sit inside narrowing scopes. This
duplicates the structure of the main inference walk. If a new expression form
is added, both walks need updating.

**Approach**: Annotate each SCC group member with its enclosing narrowing
context during the existing group_def pass in `lang_ast`. The SCC computation
already walks the dependency graph — it could carry a `Vec<NarrowBinding>` stack
through scope-introducing expressions (if-then-else, assert).

**This is a larger refactor.** Prerequisites:
- Understand `lang_ast/src/group_def.rs` (SCC computation)
- Understand how `analyze_condition` depends on name resolution but NOT on
  type information (it's purely syntactic)
- Consider whether `NarrowBinding` / `NarrowPredicate` should move to `lang_ast`
  to avoid a circular dependency, or whether the analysis stays in `lang_check`
  but is invoked from a different point.

**Recommended incremental approach**:
1. First do C1 (dedup the binding iteration)
2. Then move `analyze_condition` and supporting helpers (`expr_is_null`,
   `expr_as_local_name`, `single_static_attrpath_key`, `is_builtin_call`,
   `try_*` helpers) to a standalone function that takes `&Module` and
   `&NameResolution` rather than `&CheckCtx`. This decouples condition analysis
   from the inference context.
3. Then integrate the scope analysis into the SCC grouping pass.

**Files touched**: `lang_ast/src/narrow.rs` (new), `lang_ast/src/lib.rs`,
`lang_ast/src/nameres.rs`, `lang_check/src/narrow.rs`, `lang_check/src/infer.rs`,
`lang_check/src/infer_expr.rs`, `lang_check/src/lib.rs`

---

## Theme D: Deferred Constraint Cleanup

### ~~D1. Unify deferred constraint types~~ ✅ Done

**Effort**: Low | **Impact**: Medium | **Risk reduction**: Makes lifecycle
explicit

`DeferredConstraints` has three fields: `overloads`, `merges`, and
`deferred_overloads`. The first and third are the same type at different
lifecycle stages, managed by convention (`infer.rs:132-133`).

**What to do**:

1. Create an enum in `infer_expr.rs`:
   ```rust
   pub enum PendingConstraint {
       Overload(PendingOverload),
       Merge(PendingMerge),
   }
   ```
2. Replace `DeferredConstraints` in `lib.rs` with:
   ```rust
   pub struct DeferredConstraints {
       /// Active pending constraints for the current SCC group.
       pub active: Vec<PendingConstraint>,
       /// Carried over from previous groups for extrusion re-instantiation.
       pub carried: Vec<PendingOverload>,
   }
   ```
3. Update `resolve_pending` (`infer.rs:456-504`) to partition `active` by
   variant instead of iterating two separate lists.
4. Update `infer_scc_group` (`infer.rs:132-133`) to move unresolved overloads
   from `active` to `carried`.
5. Update `extrude` (`infer.rs:260-308`) to iterate `carried`.
6. Run tests.

**Files touched**: `lang_check/src/lib.rs`, `lang_check/src/infer.rs`,
`lang_check/src/infer_expr.rs`

---

### ~~D2. Table-driven operator dispatch~~ ✅ Done

**Effort**: Medium | **Impact**: Medium | **Risk reduction**: Centralizes
operator semantics currently spread across 3 locations

Adding or modifying an overloadable operator currently requires changes in:
- `infer_expr.rs:625-655` (immediate constraints + deferred push)
- `infer.rs:506-592` (`try_resolve_overload` partial/full phases)
- `infer.rs:719-752` (`solve_bin_op_types`)

The `+` operator has special handling in all three places.

**What to do**:

1. Define an operator spec table somewhere central (e.g. a new
   `lang_check/src/operators.rs` or at the top of `infer.rs`):
   ```rust
   struct OverloadSpec {
       /// If set, immediately constrain both operands and result to this type.
       /// None for `+` (which also handles strings/paths).
       immediate_bound: Option<PrimitiveTy>,
       /// Given concrete lhs and rhs primitive types, return the result type.
       /// None means the combination is invalid.
       resolve: fn(&PrimitiveTy, &PrimitiveTy) -> Option<PrimitiveTy>,
       /// For partial resolution: can we pin the return type early from just
       /// the lhs? (e.g., string + _ → string)
       early_ret_pin: Option<fn(&PrimitiveTy) -> Option<PrimitiveTy>>,
   }
   ```
2. Populate the table for `+`, `-`, `*`, `/`.
3. Replace the branching logic in `infer_bin_op`, `try_resolve_overload`, and
   `solve_bin_op_types` with table lookups.
4. Run tests.

**Files touched**: `lang_check/src/infer.rs`, `lang_check/src/infer_expr.rs`

---

## Theme E: Constraint System Improvements

### ~~E1. Add covariance/soundness comment for List~~ ✅ Done

**Effort**: Trivial | **Impact**: Low | **Risk reduction**: Documents a critical
assumption

`constrain.rs:112` treats lists as covariant:
```rust
(Ty::List(e1), Ty::List(e2)) => self.constrain(*e1, *e2),
```

This is sound only because Nix is pure (lists are immutable). The assumption
isn't documented. Add a comment explaining why this is correct and under what
conditions it would become unsound.

**Files touched**: `lang_check/src/constrain.rs`

---

### E2. Has-field constraints for open attrsets

**Effort**: High | **Impact**: High | **Risk reduction**: Closes a class of
silent missed errors

`constrain_attrsets` (`constrain.rs:170-178`) silently passes when a required
field is missing from an open attrset. The comment acknowledges this and
suggests "has-field" constraints.

**Approach**:

1. Add a new deferred constraint type:
   ```rust
   pub struct PendingHasField {
       /// The attrset type that should have the field.
       pub set_ty: TyId,
       /// The field name that must be present.
       pub field: SmolStr,
       /// The expected field type.
       pub field_ty: TyId,
       /// Location for error reporting.
       pub at_expr: ExprId,
   }
   ```
2. In `constrain_attrsets`, when `sub` is open and doesn't have a required
   field: emit a `PendingHasField` instead of silently passing.
3. In `resolve_pending`, try to resolve has-field constraints:
   - If the set type has become concrete/closed and lacks the field → error.
   - If the set type has the field → constrain field types.
   - If still open/unknown → keep pending.
4. Add test cases:
   - `{ x, ... }: x.y` where the function is called with `{ x = 1; }` → error
   - `{ x, ... }: x` where the function is called with `{ x = 1; y = 2; }` → ok
   - Open-set patterns where field presence can't be determined → no error

**This is a substantial change.** Read the `constrain_attrsets` function and its
callers carefully. Consider edge cases with `with` scopes and dynamic field
types.

**Files touched**: `lang_check/src/constrain.rs`, `lang_check/src/infer.rs`,
`lang_check/src/lib.rs`, `lang_check/src/tests.rs`

---

## Theme F: Canonicalization Robustness

### ~~F1. Property test for early-canonicalization stability~~ ✅ Done

**Effort**: Medium | **Impact**: High | **Risk reduction**: Validates a
correctness-critical heuristic

The early-canonicalization snapshot (`infer.rs:137-143`) captures a name's type
before `exit_level`, with a fallback at `collect.rs:531-538` if the snapshot is
a bare `TyVar`. This is a heuristic — there's no formal argument for why
`TyVar` is the right trigger.

**What to do**:

1. Write a property-based test in `lang_check/src/pbt/mod.rs` that:
   - Generates a polymorphic let-binding (e.g. `let f = x: x; in f 1`)
   - Calls the binding at multiple use-sites with different concrete types
   - Asserts that the canonical type of the binding is stable across different
     numbers and types of use-sites
   - Specifically: `f`'s type should be `a -> a`, not `int -> int` or
     `string -> string`, regardless of how it's used

2. Extend the test to cover:
   - Polymorphic bindings used 0 times (no extrusion)
   - Polymorphic bindings used 1 time (one extrusion)
   - Polymorphic bindings used N times with different types

3. If any failure is found, investigate whether `link_extruded_var` has a
   subtle bidirectional leak.

**Files touched**: `lang_check/src/pbt/mod.rs` or `lang_check/src/tests.rs`

---

### ~~F2. Unify `expand_bounds_as_union` and `expand_bounds_as_intersection`~~ ✅ Done

**Effort**: Low | **Impact**: Low | **Risk reduction**: Eliminates
near-duplicate code

These two methods in `collect.rs` are structurally identical except:
- One reads `lower_bounds`, the other `upper_bounds`
- One calls `flatten_union` / `remove_tautological_pairs`, the other calls
  `flatten_intersection` / `merge_attrset_intersection` / `has_primitive_contradiction`
- The empty-case fallback differs

They could share a generic core parameterized by polarity (easier after A1).

**What to do**:

1. Create `expand_bounds`:
   ```rust
   fn expand_bounds(&mut self, bounds: &[TyId], var_id: TyId, polarity: Polarity) -> OutputTy
   ```
2. Use `match polarity` for the differences (flatten function, normalization,
   fallback).
3. Keep the existing methods as thin wrappers if that's clearer.
4. Run tests.

**Files touched**: `lang_check/src/collect.rs`

---

## Theme G: Testing Gaps

### G1. Cross-file import inference tests

**Effort**: Medium | **Impact**: Medium

The test suite has limited coverage of `import_types` — pre-resolved types from
imported files. Add tests in `lang_check/src/tests.rs` using
`check_file_with_imports` that verify:
- Imported polymorphic types are properly isolated (constraints don't leak back)
- Imported union/intersection types are interned correctly
- Named/aliased imports preserve provenance

---

### ~~G2. Narrowing + overload interaction tests~~ ✅ Done

**Effort**: Low-Medium | **Impact**: Medium

Add tests for cases where narrowing and overload resolution interact:
- `if isInt x then x + 1 else 0` — x should be `int` in then-branch, `+`
  should resolve to `int`
- `if isNull x then 0 else x + 1` — x should be `~null` in else-branch
- Nested narrowing with arithmetic: `if isInt x then (if isInt y then x + y else 0) else 0`

---

### ~~G3. Negation + intersection contradiction tests~~ ✅ Done

**Effort**: Low | **Impact**: Low-Medium

Add tests verifying that contradictions are detected:
- `int & ~int` → currently `TyVar`, should be `never` after A2
- `int & ~number` → contradiction (Int <: Number)
- `float & ~number` → contradiction
- `string & ~null` → NOT a contradiction

---

## Recommended Execution Order

Quick wins (do first, each is a single short session):

1. ~~**E1** — Add list covariance comment (trivial)~~ ✅
2. ~~**A1** — Polarity enum (low effort, immediate readability win)~~ ✅
3. ~~**B2** — Unify find_concrete variants (low effort, removes duplication)~~ ✅
4. ~~**C1** — Dedup narrow walk_for_narrow_scopes (low effort)~~ ✅
5. ~~**D1** — Unify deferred constraint types (low effort)~~ ✅

Medium tasks (each is a full session):

6. ~~**G2, G3** — Test gap coverage~~ ✅
7. ~~**F2** — Unify expand_bounds (easy after A1)~~ ✅
8. ~~**D2** — Table-driven operator dispatch~~ ✅
9. ~~**A2** — Add Bottom type~~ ✅
10. ~~**F1** — Early-canonicalization property test~~ ✅

Larger refactors (plan before starting):

11. ~~**B1** — Extract TypeTable~~ ✅
12. ~~**E2** — Has-field constraints~~ ✅
13. ~~**C2** — Move narrowing into SCC grouping~~ ✅
14. **G1** — Cross-file import tests
