# Reducing Canonicalization Memory Blowup

## Problem Statement

Canonicalization (`lang_check/src/collect.rs`) can exhibit exponential memory
growth. The root cause is in inference (extrusion), but canonicalization is
where the memory bill comes due.

### Why it happens

Each call to `extrude()` (`infer.rs:480`) creates fresh copies of **all**
polymorphic type variables reachable from the extruded type. The per-call-site
cache (`FxHashMap<TyId, TyId>`) prevents re-visiting within one extrusion, but
across call sites identical structure is re-copied.

With nested polymorphic calls, variable count grows as **B^D** (B = calls per
nesting level, D = nesting depth):

```nix
let
  f = x: g x + g x;    # 2 copies of g's vars
  h = y: f y + f y;     # 2 copies of f's vars, each containing 2 copies of g's = 4
in h                     # total: 4 copies of g's variables
```

Additionally, `link_extruded_var` (`infer.rs:801`) recursively extrudes each
bound and calls `add_lower_bound`/`add_upper_bound`. In real nixpkgs files
(e.g. `strings.nix`) this creates millions of type entries and consumes
gigabytes of RSS.

### How canonicalization amplifies the problem

1. **Every fresh TyId gets its own cache entry** in `Canonicalizer.cache`
   (keyed by `(TyId, Polarity)`). Exponential variable count = exponential
   cache entries.

2. **Normalization helpers run quadratic pairwise checks** on flattened
   union/intersection member lists:
   - `remove_tautological_pairs` (`collect.rs:478`): O(positives * negated_inners)
   - `absorb_subsumed_union_members` (`collect.rs:555`): O(attrsets^2)
   - `has_type_contradiction` (`collect.rs:732`): O(positives * negated + positives^2)
   - `factor_shared_from_intersection` (`collect.rs:628`): O(unions^2 * members_per_union)

3. **`negate_output_ty` (`collect.rs:443`) operates on `OutputTy`, not `TyId`**,
   so the `Canonicalizer.cache` doesn't help. Large unions under negation
   produce equally large intersections via De Morgan.

4. **Variable isolation** (`constrain.rs:317`) wraps targets in
   `Union(sup, Neg(C))`. Distinct narrowing guards produce distinct Neg types,
   growing member counts linearly with narrowing sites.

5. **`merge_attrset_intersection` (`collect.rs:945`)** merges N attrsets into
   one with up to N*M fields. Nixpkgs attrsets can have hundreds of fields.


## Existing Mitigations

- **Deadline mechanism** (`collect.rs:37-91`): degrades to TyVar when time runs out
- **`(TyId, Polarity)` cache** (`collect.rs:60`): prevents recomputation of same TyId
- **Cycle detection** (`collect.rs:99`): `in_progress` set prevents infinite recursion
- **TyRef interning** (`arc_ty.rs:98-144`): primitives/Top/Bottom share Arcs
- **`dedup_bounds`** (`storage.rs:144`): removes duplicate bounds after SCC groups
- **`variable_free` set** (`infer.rs:594`): skips extrusion for variable-free subtrees
- **`find_pinned_concrete`** (`infer.rs:627`): extrudes concrete type instead of
  creating fresh variable when a variable is pinned between identical bounds
- **`compact_pinned_variables`** (`type_table.rs:242`): replaces fully-determined
  variables with concrete types in-place after each SCC group (-85% RSS on
  strings.nix)
- **Union absorption check** (`constrain.rs:351`): prevents redundant Union wrapping
  in variable isolation


## Proposed Approaches

Listed in recommended implementation order (smallest-first stacking strategy).

---

### C: Bounds-Signature Dedup in Canonicalization

**Effort:** ~1 day. Only touches `collect.rs`.

**Idea:** The canonicalization cache is keyed by `(TyId, Polarity)`. Two
different TyIds with identical bounds produce identical `OutputTy` but are
cached separately. Add a secondary cache keyed by bounds signature.

```rust
struct Canonicalizer<'a> {
    cache: FxHashMap<(TyId, Polarity), OutputTy>,
    // NEW: bounds-signature -> OutputTy dedup cache
    bounds_cache: FxHashMap<(u64, Polarity), OutputTy>,
}
```

In `canonicalize_inner` for variables:

```rust
let sig = hash_bounds(&v.lower_bounds, &v.upper_bounds);
if let Some(cached) = self.bounds_cache.get(&(sig, polarity)) {
    return cached.clone();
}
// ... normal canonicalization ...
self.bounds_cache.insert((sig, polarity), result.clone());
```

**Why it helps:**
- When extrusion creates N copies of a polymorphic variable with identical
  bounds, canonicalization computes the OutputTy once and shares it N times.
- Memory: N separate OutputTy allocations -> 1 allocation + N-1 Arc clones.
- Time: N recursive bound-expansions -> 1 expansion + N-1 hash lookups.

**Limitations:**
- Only exact TyId-level matches work. Bounds that are structurally equivalent
  but have different TyIds won't match.
- Need care with variables that have the same bounds but different Named
  wrappers.
- Hash collisions (use sorted bounds TyIds as signature — cheap since TyId is u32).

---

### D: Lazy Bounds Propagation in `link_extruded_var`

**Effort:** ~2-3 days. Touches `storage.rs`, `infer.rs`, `constrain.rs`.

**Idea:** Currently `link_extruded_var` (`infer.rs:819-825`) immediately
extrudes and installs all bounds from the original into the fresh variable.
Instead, defer this: record that "fresh inherits bounds from original" and only
propagate when the fresh variable is actually constrained.

```rust
struct TypeVariable {
    lower_bounds: SmallVec<[TyId; 4]>,
    upper_bounds: SmallVec<[TyId; 4]>,
    level: u32,
    /// Deferred bounds source — populated by extrusion, resolved on first constrain.
    deferred_source: Option<DeferredBounds>,
}

struct DeferredBounds {
    original: TyId,
    polarity: Polarity,
    extrude_cache: Arc<FxHashMap<TyId, TyId>>,
}
```

In `constrain()`, when encountering a variable with `deferred_source`:

```rust
if let Some(deferred) = v.deferred_source.take() {
    self.resolve_deferred_bounds(var_id, deferred);
}
// Then proceed with normal constraint logic
```

**Why it helps:**
- Variables immediately pinned (e.g. `id 42` pins `x' = int`) never need to
  extrude bounds from the original — the constraint `int <: x'` resolves directly.
- Variables never constrained at all (dead code, unused fields) skip all work.
- SESSION.md notes the big cost is constraint propagation triggered by bounds
  copying — this defers it entirely.

**Hard parts:**
- The extrude cache is per-call-site and currently stack-allocated. For deferred
  resolution it needs to outlive the extrude call -> `Arc<FxHashMap>` or similar
  shared ownership.
- Multiple variables from the same extrusion share the same cache.
- Interaction with `compact_pinned_variables` — deferred variables may look
  "empty" and get incorrectly compacted.

---

### B: Copy-on-Constrain Variables

**Effort:** ~3-5 days. Mainly touches `storage.rs`, `constrain.rs`, `infer.rs`,
`collect.rs`.

**Idea:** Variables created by extrusion start as lightweight **proxies** that
share the original's bounds. They're only "materialized" (given their own
independent bounds) when a new constraint arrives.

```rust
enum TypeEntry {
    Variable(TypeVariable),
    Concrete(Ty<TyId>),
    /// Proxy to another variable. Shares bounds until constrained.
    Proxy { original: TyId, polarity: Polarity },
}
```

How `constrain()` handles proxies:

```rust
// When encountering a Proxy:
(true, _) if is_proxy(sub) => {
    let original = self.types.get_proxy_original(sub);
    self.materialize_proxy(sub, original, polarity);
    self.constrain(sub, sup)
}
```

How canonicalization handles proxies:
- Unmaterialized proxy at polarity P -> `canonicalize(original_id, P)` -> cache
  hit on original -> no extra OutputTy allocation.

**Why it helps:**
- Variables that pass through unconstrained (common in large attrset pipelines)
  are never materialized — they're just pointers.
- Canonicalization benefits directly: proxy -> cache hit on original.
- Constraint propagation only happens when actually needed.

**Hard parts:**
- Transitive proxies (proxy of a proxy) need chain resolution like union-find.
- When materializing, must copy bounds that may have changed since generalization.
- Interaction with `compact_pinned_variables` — proxies that resolve to pinned
  variables should be collapsed.

---

### A: Compact Type Schemes

**Effort:** ~1-2 weeks. Touches `infer.rs`, `infer_expr.rs`, `storage.rs`,
`lib.rs` (CheckCtx), `collect.rs`.

**Idea:** After inferring an SCC group, instead of storing a raw `TyId` in
`poly_type_env`, compute and store a **type scheme**: a compact template that
records only the polymorphic structure.

```rust
struct TypeScheme {
    /// The polymorphic variables in this scheme, in traversal order.
    poly_vars: Vec<SchemeVar>,
    /// The type structure with polymorphic variable positions replaced
    /// by indices into poly_vars.
    skeleton: CompactTy,
}

struct SchemeVar {
    lower_bounds: SmallVec<[CompactTy; 4]>,
    upper_bounds: SmallVec<[CompactTy; 4]>,
}
```

Instantiation at a use site:
1. Create `k` fresh variables (one per `SchemeVar`).
2. Walk the skeleton, substituting fresh TyIds for scheme variable indices.
3. Install each fresh variable's bounds by substituting the same mapping into
   the scheme's bound templates.
4. Link fresh <-> original as before.

**Why it helps:**
- The skeleton is computed **once** at generalization, not re-traversed at every
  use site.
- Variable-free subtrees in the skeleton are shared `CompactTy` nodes — no
  traversal needed.
- Per-use-site cost is **O(k)** where k is the number of polymorphic variables,
  not O(entire type graph).
- The scheme is **self-contained** — it doesn't reference the live bounds graph,
  so there's no cascade risk.

**What changes:**
- `poly_type_env: FxHashMap<NameId, TyId>` -> `FxHashMap<NameId, TypeScheme>`
- `extrude()` replaced by `instantiate_scheme()`.
- `link_extruded_var` replaced by direct bounds installation from the scheme.
- Early canonicalization can operate on the scheme directly.

**Hard parts:**
- Designing `CompactTy` so it's independent of the live `TypeStorage`.
- Handling recursive types (self-referencing schemes need explicit fix-point).
- Deferred overload re-instantiation needs adaptation (currently walks the
  extrude cache).
- Mutual recursion in SCC groups — scheme for `f` may reference `g`'s
  polymorphic variables.


## Stacking Strategy

Implement in order C -> D -> B -> A:

1. **C** is a ~1-day canonicalization-only change that immediately reduces memory
   for the common case of duplicated variables. No inference changes.

2. **D** cuts inference-time cost of extrusion. Variables that get immediately
   pinned skip the expensive bounds-copying step entirely.

3. **B** if C+D aren't enough. More surgical than A, preserves the SimpleSub
   architecture.

4. **A** for a cleaner long-term design if the incremental approaches hit
   diminishing returns.


## Background: How Extrusion Works Today

Each `extrude()` call (`infer.rs:480`):

1. Creates a per-call-site cache: `FxHashMap<TyId, TyId>` with capacity 64.
2. Calls `extrude_inner()` recursively on the type graph.
3. **Fast paths** (no fresh variables):
   - `variable_free` types (`infer.rs:594`): O(1) set check, skip entire subtree.
   - Non-polymorphic variables, `level < current_level` (`infer.rs:602`): return as-is.
   - Primitives/TyVar (`infer.rs:605`): leaf types, return and mark variable-free.
4. **Polymorphic variables** (`v.level >= current_level`, `infer.rs:620`):
   - If pinned (`find_pinned_concrete`): extrude the concrete type instead.
   - Otherwise: create fresh variable (`new_var()`), cache it, call
     `link_extruded_var()` to copy polarity-appropriate bounds.
5. **Concrete types** (`infer.rs:654`): recurse into children. If all children
   unchanged, reuse original TyId (macros `extrude_single!`/`extrude_binary!`).
6. Re-instantiate deferred overloads carried under the extruded name
   (`infer.rs:489-569`): fixed-point loop creating fresh overloads per call site.

`link_extruded_var()` (`infer.rs:801`):
- Positive: `original <: fresh`, copy original's lower bounds (extruded) into fresh.
- Negative: `fresh <: original`, copy original's upper bounds (extruded) into fresh.
- Each bound is recursively extruded via `extrude_inner()`.


## Background: How Canonicalization Works Today

`Canonicalizer` (`collect.rs:42`) maintains:
- `cache: FxHashMap<(TyId, Polarity), OutputTy>` — memoization.
- `in_progress: FxHashSet<(TyId, Polarity)>` — cycle detection.
- `deadline`/`op_counter`/`deadline_exceeded` — graceful timeout.

Core algorithm (`canonicalize` at `collect.rs:73`):
1. Check cache -> return memoized.
2. Check `in_progress` -> if cycle, return `TyVar(id)`.
3. Check deadline (every 512 ops) -> if exceeded, return `TyVar(id)`.
4. Call `canonicalize_inner`:
   - **Variables**: check for Named bounds (polarity-agnostic), then expand
     bounds by polarity (positive = union of lower bounds, negative =
     intersection of upper bounds) via `expand_bounds()`.
   - **Concrete types**: recurse into children with polarity (flip for lambda
     params).

Two-phase design:
- **Early canonicalization** (`infer.rs:308`): snapshot after each SCC group,
  before use-site extrusions contaminate bounds.
- **Late canonicalization** (`collect.rs:1041`): after all inference, for names
  where early snapshot was uninformative (bare TyVar).


## Key Files

| File | Relevant sections |
|------|-------------------|
| `lang_check/src/collect.rs` | Canonicalizer, expand_bounds, normalization helpers |
| `lang_check/src/infer.rs:480-826` | extrude, extrude_inner, link_extruded_var |
| `lang_check/src/infer.rs:233-369` | infer_scc_group orchestration |
| `lang_check/src/infer_expr.rs:485,958` | Extrusion call sites (name references, attrset construction) |
| `lang_check/src/constrain.rs` | Constraint propagation, variable isolation |
| `lang_check/src/storage.rs` | TypeVariable, TypeStorage, bounds manipulation |
| `lang_check/src/type_table.rs` | TypeTable, variable_free, compact_pinned_variables |
| `lang_check/src/lib.rs:534-618` | CheckCtx, poly_type_env, DeferredConstraints |
| `lang_ty/src/arc_ty.rs` | OutputTy, TyRef (Arc-wrapped), interning |


## References

- Parreaux, "The Simple Essence of Algebraic Subtyping" (ICFP 2020) — extrusion design
- Chau & Parreaux, "Simple Essence of Boolean-Algebraic Subtyping" (POPL 2026) — BAS extension
- Parreaux & Chau, "MLstruct" (OOPSLA 2022) — negation + pattern matching
- `github.com/fo5for/sebas` — BAS reference implementation
- `github.com/LPTK/simple-sub` — original SimpleSub Scala implementation
