# Arena-Interned OutputTy — Remaining Work

## Original Goal

Replace `TyRef(Arc<OutputTy>)` with arena-indexed `TyRef(la_arena::Idx<OutputTy>)` + hash-consing
to eliminate per-node allocation overhead, halve reference size (4 bytes vs 8), enable O(1) equality
via index comparison, and improve cache locality. Target: nixpkgs-test should not OOM at 16 GB.

## What's Done

All production code compiles with 0 errors, 0 warnings. End-to-end type inference works correctly.

### Passing tests
- **LSP: 313/313** — all e2e tests pass
- **lang_ty: 207/210** (3 skipped, 0 failed)
- **CLI: 3/3**
- **comment_parser: all pass**
- Smoke test: `tixc test/basic.nix` produces correct types

### Files changed (production)
| Crate | Files |
|-------|-------|
| `lang_ty` | `arena.rs` (new), `arc_ty.rs`, `attrset.rs`, `simplify.rs`, `arbitrary.rs`, `lib.rs` |
| `lang_check` | `collect.rs`, `lib.rs`, `constrain.rs`, `infer.rs`, `infer_expr.rs`, `imports.rs`, `coordinator.rs`, `aliases.rs`, `diagnostic.rs` |
| `lsp` | `hover.rs`, `completion.rs`, `ty_nav.rs`, `signature_help.rs`, `inlay_hint.rs`, `diagnostics.rs`, `code_actions.rs`, `type_def.rs`, `state.rs`, `server.rs` |
| `cli` | `main.rs`, `check.rs` |

### Key design decisions implemented
- `TyRef = Idx<OutputTy>` (4-byte Copy arena index)
- `TypeArena` with hash-consing (`FxHashMap<OutputTy, TyRef>`)
- `OwnedTy { arena: Arc<TypeArena>, root: TyRef }` for cross-file types
- `InferenceResult { arena: Arc<TypeArena>, name_ty_map: ArenaMap<NameId, TyRef>, ... }`
- `FileSignature { root_ty: OwnedTy }` (compacted arena)
- `Ty::Frozen(OwnedTy)` for lazy import materialization
- `import_types: HashMap<ExprId, OwnedTy>`
- `canonicalize_standalone` returns `(TypeArena, TyRef)`
- `early_canonical` stores `(TypeArena, TyRef)` per name
- All display goes through `TypeArena::display(ty)` / `display_truncated(ty, config)`
- `RawTy` intermediate for proptest generation → `ArbitraryType { arena, root }`

## What's Left — 121 test compilation errors

All remaining errors are in **test code only**. Production code is complete.

### 1. `collect.rs` tests — 58 errors

**Two patterns:**

a) **`(TypeArena, TyRef)` doesn't impl `PartialEq`** (3 sites, lines ~1499, 1526, 1884):
`canonicalize_standalone` returns `(TypeArena, TyRef)`. Tests compare with `assert_eq!`.
Fix: destructure and compare the `OutputTy` values:
```rust
let (result_arena, result_ty) = canonicalize_standalone(&table, ty_id, Positive);
assert_eq!(result_arena[result_ty], expected_output_ty);
```

b) **Double mutable borrow in `arc_ty!`/helper calls** (~55 sites):
`isect(&mut a, vec![neg(&mut a, int()), neg(&mut a, string())])` borrows `a` mutably
multiple times. Fix: pre-compute each element:
```rust
let neg_int = neg(&mut a, int());
let neg_str = neg(&mut a, string());
let expected = isect(&mut a, vec![neg_int, neg_str]);
```
The pattern is the same for `remove_tautological_pairs(&a, ...)`, `merge_attrset_intersection(&mut a, ...)`,
`remove_redundant_negations(&a, ...)`, `factor_shared_from_intersection(&mut a, ...)`,
`absorb_subsumed_union_members(...)` test calls that nest arena-borrowing helpers.

### 2. `pbt/mod.rs` — 44 errors

`OutputTy` no longer implements `Arbitrary`. The PBT module needs to use `ArbitraryType`
from `lang_ty::arbitrary` instead.

Key changes:
- `any::<OutputTy>()` → `any::<ArbitraryType>()` (returns `ArbitraryType { arena, root }`)
- All `OutputTy` method calls → `TypeArena` method calls:
  - `.free_type_vars()` → `arena.free_type_vars(ty)`
  - `.normalize_vars()` → `arena.normalize_vars(ty)`
  - `.normalize_set_ops()` → `arena.normalize_set_ops(ty)`
  - `.has_type_vars()` → `arena.has_type_vars(ty)`
  - `.has_non_primitive_lambda_param()` → `arena.has_non_primitive_lambda_param(ty)`
  - `.contains_bare_tyvar()` → `arena.contains_bare_tyvar(ty)`
  - `.contains_union_or_intersection()` → `arena.contains_union_or_intersection(ty)`
  - `.contains_intersection()` → `arena.contains_intersection(ty)`
  - `.contains_neg()` → `arena.contains_neg(ty)`
  - `.has_shared_tyvar_across_lambda_params()` → `arena.has_shared_tyvar_across_lambda_params(ty)`
- `.offset_free_vars(&mut num)` → `arena.offset_free_vars(ty, &mut num)`
- `.spread_free_vars(&mut num)` → `arena.spread_free_vars(&attr, &mut num)`
- `format!("{ty}")` → `format!("{}", arena.display(ty))`
- Pattern matches on `OutputTy` variants: `match ty { OutputTy::Lambda { .. } => ... }` → `match &arena[ty] { ... }`

### 3. `coordinator.rs` tests — 11 errors

Already partially fixed (helper `make_sig` and `owned_ty_eq` added). Remaining errors are
test sites that still construct `FileSignature` with raw `OutputTy` instead of using `make_sig()`.
Grep for `OutputTy::Primitive` in the test section and replace with `make_sig(OutputTy::Primitive(...))`.

### 4. `pbt/stub_compose.rs` — 8 errors

Similar to pbt/mod.rs — uses `OutputTy` methods and `TyRef::from()`. Needs arena context.
Also has `RootTy` vs `OutputTy` type mismatches from the tests.rs `RootTy` wrapper that
was introduced.

## Phase 6 (optional, separate PR): Data layout optimization

Not started. From the original plan:

1. `AttrSetTy.fields`: `BTreeMap<SmolStr, TyRef>` → `Vec<(SmolStr, TyRef)>` (sorted, binary search).
   With TyRef at 4 bytes, each entry is 28 bytes vs BTreeMap's ~48+ bytes per entry.
2. `Union`/`Intersection`: `Vec<TyRef>` → `SmallVec<[TyRef; 4]>` (avoids heap alloc for common 2-4 member case).
3. `optional_fields: BTreeSet<SmolStr>` → `SmallVec<[SmolStr; 4]>` (sorted, typically small).

## Verification Checklist

Once all tests compile:

1. `cargo nextest run` — all existing tests pass (semantic behavior unchanged)
2. `./scripts/pbt.sh 50000` — PBT passes with arena-backed types
3. `tixc --timing test/strings.nix` — RSS should drop significantly (target: <500 MB from ~1.2 GB)
4. `nixpkgs-lib-test --parallel --release --timing` — verify no regression in type results, check RSS
5. `nixpkgs-test --release --timing -j 4` — target: should not OOM at 16 GB
6. LSP e2e tests pass: `cargo nextest run -p tix-lsp`
