## Known Issues & Future Work

Items not tracked in backlog — either too small for a task, known limitations
by design, or informational notes.

### Canonicalization / Type Display

- ~~**Let-binding loses union type**~~: Fixed via `resolve_to_single_concrete_id`
  which compares type heads instead of TyIds, preserving unions through
  poly_type_env. PBT workarounds for union let-binding also removed.

- Early canonicalization captures clean polymorphic types for name bindings, but
  the root expression type still shows contaminated types for inherited names.
  The inherit creates a new NameId whose type comes from extruding the original,
  and that extruded reference picks up use-site bounds. A full fix would propagate
  early-canonical types through expression-level canonicalization.

- The upper-bound fallback in canonicalization (variables with only primitive upper
  bounds display as that primitive in positive position) may be too aggressive in
  some edge cases. Monitor for false positives in PBT.

### Known Limitations (by design)

- **Deferred builtins** (`add`/`sub`/`mul`/`div`, `baseNameOf`/`dirOf`,
  `derivation`, `genericClosure`, fetch functions) return fresh type variables —
  need type system extensions (`number` union, `stringish` union). Won't cause
  errors but provide no type info.

- **`builtins` attrset synthesized fresh** on every reference. Correct but
  potentially expensive. Could cache and extrude.

- **Cyclic imports** degrade gracefully (unconstrained type variable + diagnostic)
  but don't support cross-file mutual recursion.

- **Unconstrained variables** cause pathological constraint propagation. Deadline
  mechanism (5s imports, 10s top-level) is the safety net; real fix is stubs.

- **Lambda parameter completion** limited by SimpleSub's extrusion-based
  generalization — call-site types don't flow back to parameter variables.

- **rnix error recovery** on incomplete code (`pkgs.` with no field) can cascade,
  mangling subsequent expressions. Upstream issue.

- **Rename "not renameable" in editor** (FIXED): Root cause was `name_at_position`
  using only `right_biased()` for `token_at_offset`. When the cursor is at the end
  of an identifier (a token boundary), `right_biased()` picks the whitespace token
  instead of the identifier. VS Code sends cursor positions at the end of words.
  Fix: try right-biased first, then fall back to left-biased. Regression test:
  `references::tests::name_at_end_of_identifier`.

### PBT

- **Shared type vars across lambda scopes**: PBT generator can produce types like
  `Lambda(TyVar(8) -> Lambda(TyVar(8) -> Int))` where both params share a variable,
  but the code generator creates independent shadowing params whose types are correctly
  inferred as distinct variables. Comparison then fails because the generated code
  can't represent shared-variable types. Need to either filter these cases or generate
  Nix code that actually links the params (e.g. `x: y: x + y` with a constraint).

### Minor Untracked Items

- `test/strings.nix`: `nameFromURL :: String -> String` annotation has wrong arity
  (1 arg, function takes 2). Detected and skipped with a warning.

- `test/null_default.nix` line 45: `lib.findFirst (k: arg ? ${k}) null ...` errors
  because `findFirst` is not stubbed. Unrelated to narrowing.

- `NameKind` classification: files with top-level lambda `{ pkgs ? <nixpkgs> }:`
  produce `PlainAttrset` for inner let-binding names. Could investigate.

- `miette` in `lang_ast` should be dev-dependency only.

- `BindingValueKind::ImplicitSet` (`lower.rs`): never constructed, dead code.

- `collect.rs` is ~1756 lines — could benefit from phase separation.

- Dynamic attrset keys not tracked in recursive sets (`nameres.rs`): could cause
  incorrect SCC grouping in edge cases.

- Extrude carried-overload loop is O(n^2) (`infer.rs`): could be linear with
  worklist approach.

- Stale analysis name lookup (`completion.rs`): `find_name_type_by_text()` returns
  first match when source_map fails, may pick wrong shadowed binding.

- No tests for chain re-analysis (A→B→C): requires full async analysis loop.

- `nix build .#stubs` emits `system.stateVersion is not set` warning.

- Home Manager flake mode (`gen-stubs home-manager --flake`) untested end-to-end.

- `LSP LineIndex` UTF-16 fix was applied (commit 0fe9b77) — verify it covers all
  edge cases.

### Memory Profile — `tix check` with parallel inference

#### Small project (test/nixos_fixture, 5 files)

Profiled with DHAT. Peak heap: ~50 MB. Dominated by `OutputTy::map_children` (50%),
canonicalization (18%), Arc wrapping (10%).

#### Full stubs (TIX_BUILTIN_STUBS with 266K-line stubs)

**Before optimizations** (commit a018cb3, 40 files, `-j 4`):

```
Without TIX_BUILTIN_STUBS:  200 MB RSS,  0.4s
With    TIX_BUILTIN_STUBS: 16.2 GB RSS, 21.1s   ← 80x memory increase
```

**After optimizations** (commit ca201cb, 32 files `test/`, 5 files `test/nixos_fixture/`):

```
32 files, no stubs:          123 MB RSS, 0.19s
32 files, 266K-line stubs:   312 MB RSS, 0.83s   ← 2.5x (was 80x)
 5 files, no stubs:           94 MB RSS
 5 files, 266K-line stubs:   361 MB RSS, 0.73s
```

52x reduction (16.2 GB → 312 MB) from four changes:

1. **`normalize_vars` short-circuit** — skip full tree walk + rebuild for concrete
   types with no TyVar nodes (the common case for NixOS config attrsets).
2. **CoW for `TypeAliasRegistry`** — `Arc<TypeAliasRegistry>` in `CheckCtx`, only
   clone when inline aliases or context loading needed. Eliminates N deep clones.
3. **Early `InferenceResult` drop** — `RenderableResult` captures only diagnostics;
   `InferenceResult` (full OutputTy maps) dropped inside `par_iter` closure.
4. **Primitive `TyRef` interning** — static cache for all 8 primitives + Top + Bottom,
   routed through `From<OutputTy>` so every `TyRef` construction site benefits.

**After further optimizations** (commit 58701fc):

```
With analyze globs (6 files): 639 MB RSS, 1.8s   ← from 6.8 GB / 18.5s
All files (40 files):         3.9 GB RSS, 16.3s  ← from 6.8 GB / 18.5s
```

Three changes: concrete Ty::Union/Ty::Inter in intern_parsed_ty, variable_free cache
for extrusion short-circuit, discover_all_nix_files respects [project] analyze globs.

**Remaining memory bottleneck — constraint cascade in extrusion (investigated):**

`test/strings.nix` alone uses 1.8 GB RSS / 9.35M type entries. Profile breakdown:
- SCC groups: 1.88M slots (1.7s). Group 181 (`f` = levenshtein helper) creates 1.49M.
- `infer_root.infer_expr`: +7.47M slots (2.6s) — from extruding 104 poly bindings.
- `infer_root.resolve_pending`: 0 new slots but 6.5s — pure constraint traversal.
- Canonicalization: 3.4s on 9.35M entries.

Root cause: 4 bindings (`concatImapStrings`, `concatImapStringsSep`, `elemAt`,
`genList`) each create ~1.87M entries from a single `extrude()` call. The extrusion
itself only creates ~7 new type entries, but `link_extruded_var` triggers constraint
propagation through the entire bounds graph (cascading through the 1.88M entries from
the levenshtein SCC group). Each extrusion creates O(graph_size) constrain_cache
entries. This is inherent to the bounds-based SimpleSub approach — the constraints must
propagate to maintain soundness.

**After bounds graph compaction** (commit 85e75de, branch `bounds-graph-compaction`):

```
strings.nix with stubs:      278 MB RSS, 1.5s    ← from 1.8 GB / ~15s (-85% RSS, -90% time)
All files, -j 4:             2.6 GB RSS, 8.0s    ← from 3.9 GB / 16.3s (-33% RSS, -51% time)
All files, -j 16:            5.0 GB RSS, 8.1s    (not directly comparable to -j 4 baseline)
```

Compaction replaces fully-determined type variables (pinned between identical
concrete bounds) with their concrete type in-place after each SCC group. This
eliminates variables that extrusion treats as polymorphic but are effectively
constants. 39,920 variables pinned across 179 SCC groups in the full test suite.

Remaining mitigations (not yet implemented):
- **Lazy bounds propagation**: Don't propagate bounds through link_extruded_var
  immediately; instead record the link and propagate on demand when the fresh
  variable is actually constrained at a use site. Requires careful analysis of
  when bounds observation occurs.
- **Per-file deadline**: strings.nix takes 1.5s now; still worth capping for
  pathological inputs. Already have the deadline mechanism but it's per-project.

**Other remaining optimization (deferred):**

- **BTreeMap → sorted Vec for output `AttrSetTy`:** Fields are built once, read-only
  after. `Vec<(SmolStr, TyRef)>` with binary search would halve allocation overhead.
  Deferred because it's invasive (~15 files across 4 crates) and current numbers are
  acceptable.

<details>
<summary>Pre-optimization heaptrack breakdown (14.8 GB heap)</summary>

| Peak   | Function                            | What |
|--------|-------------------------------------|------|
| 3.49 GB | `Iterator::Map::fold` (in `map_children`) | BTreeMap rebuild via `.map().collect()` |
| 2.97 GB | `TyRef::from(OutputTy)`             | 40M Arc allocs for OutputTy nodes |
| 1.38 GB | `BTreeMap::from_iter`               | New BTreeMaps for attrset fields |
| 1.09 GB | `RawVec::finish_grow`               | Vec growth during inference |
| 889 MB  | `BTreeMap::VacantEntry::insert`     | BTreeMap node insertions |
| 872 MB  | `OutputTy::map_children` (direct)   | map_children itself |
| 848 MB  | `BTreeMap::clone::clone_subtree`    | Deep-cloning BTreeMaps |
| 623 MB  | `BTreeMap::from_iter` (2nd mono)    | Another monomorphization |
| 583 MB  | `Iterator::Map::fold` (2nd mono)    | Another call chain |
| 227 MB  | `BTreeMap::insert_recursing`        | B-tree node splits |

</details>

### Known Performance Characteristics

Intentional O(n^2) trade-offs, acceptable for typical Nix code sizes:

- **Deferred overload re-instantiation** (`infer.rs`): fixed-point loop, bounded
  by overload chain depth (typically 1-3).
- **Attrset subsumption** (`collect.rs`): pairwise comparison in union
  simplification. Small k in practice.
- **Pending constraint resolution** (`infer.rs`): swap-and-filter loop, converges
  in 2-3 passes.
- **Conservative union routing** (`constrain.rs`): when both union members are
  variables, constraints are routed to both. Sound but may create unnecessary bounds.

### DX Audit: Untracked Items

- **No incremental/cached CLI mode.** Salsa only used by LSP.
- **Stub type alias names are global.** Two teams creating `type Config = {...}`
  collide silently. No namespace/scoping mechanism.
- **No auto-freshness check for stubs.** `verify-stubs` exists but isn't
  automatic. No CI integration for drift detection.
- **Custom builder abstractions** need manual stubs or annotations per-file.
  No way to auto-derive `@context` from internal libraries.
- **No watch mode in CLI** (requires external `watchexec`).
- **gen-stubs nixos is slow** (full `nix eval`, no incremental).
- **Timeout diagnostic** says what's missing but not how to fix it.
- **No workspace/multi-root LSP support.**
- **No CONTRIBUTING.md** for potential contributors.
- **No recursive type aliases** in `.tix` files.

### DX Audit: What Works Well

Strengths to preserve during future work:

- Core type inference: row polymorphism, union types, narrowing, let-polymorphism.
- Stubs: clean `.tix` syntax, module→type-alias system, ~500+ lib declarations.
- LSP: 14 features including code actions, semantic tokens, signature help.
- Error messages: miette formatting, "did you mean?", source context.
- Narrowing: `builtins.isString`, `x ? field`, `x == null`, `assert`, boolean
  combinators. Catches bugs nothing else can.
- `tix.toml` context system: glob-based context assignment.
- `gen-stubs nixos --descriptions`: option descriptions in LSP hover.
- `@callpackage` context: zero-annotation types for nixpkgs packages.
