## Known Issues & Future Work

Items not tracked in backlog — either too small for a task, known limitations
by design, or informational notes.

### Canonicalization / Type Display

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

- **Unconstrained variables** cause pathological constraint propagation. RSS memory
  limit is the safety net; real fix is stubs.

- **Lambda parameter completion** limited by SimpleSub's extrusion-based
  generalization — call-site types don't flow back to parameter variables.

- **rnix error recovery** on incomplete code (`pkgs.` with no field) can cascade,
  mangling subsequent expressions. Upstream issue.

- **Narrowing through `with lib` not recognized**: `with lib; isBool val` doesn't
  trigger narrowing because the `with` scope resolution can't trace back to the
  builtin predicate. Affects nixpkgs modules using `with lib;` pattern (e.g.,
  privoxy.nix, knot.nix). Would need `is_builtin_call` to handle WithExprs.

- **`//` merge errors on cross-file variable types**: E004 "both sides must be
  attrsets" can fire on patterns like `ffmpeg-base.meta // { ... }` where the LHS
  type comes from a callPackage/import that doesn't resolve to a concrete AttrSet
  during deferred merge resolution. The Named-wrapping case (type aliases) was
  fixed in `bd01f7d`, the Frozen-wrapping case (cross-file imports) was fixed by
  interning Frozen types in `try_resolve_merge`, but the unresolved-variable case
  remains: the diagnostic renders resolved bounds (showing both sides as attrsets),
  but at resolution time the types are still variables.

- **`int + int` produces `InvalidBinOp` in isolated warmup context**: When running
  inference via `run_inference()` on `let b = import ./b.nix; in b + 1` where b.nix
  evaluates to `42`, the `+` operator produces a spurious `InvalidBinOp` diagnostic
  with both operands typed as `int`. May be related to overload resolution seeing
  the import's type after coordinator lookup vs direct inference.

- **Angle bracket subpaths beyond `<nixpkgs>` and `<nixpkgs/lib>`** are not
  resolved. Paths like `<nixpkgs/nixos/lib/eval-config.nix>` still produce
  E012. Could be extended by mapping more subpaths to appropriate types.

- **Narrowing through variable binding** (`enabled = x != null; if enabled then x.foo`)
  does not narrow `x`. Only direct `if x != null then x.foo` works. This means
  functions with `? null` defaults must use direct conditions, not intermediate
  boolean bindings, to avoid false type errors on field access.

### Minor Untracked Items

- `test/strings.nix`: `nameFromURL :: String -> String` annotation has wrong arity
  (1 arg, function takes 2). Detected and skipped with a warning.

- `test/null_default.nix` line 45: `lib.findFirst (k: arg ? ${k}) null ...` errors
  because `findFirst` is not stubbed. Unrelated to narrowing.

- `NameKind` classification: files with top-level lambda `{ pkgs ? <nixpkgs> }:`
  produce `PlainAttrset` for inner let-binding names. Could investigate.

- `miette` in `lang_ast` should be dev-dependency only.

- `collect.rs` is ~2300 lines — could benefit from phase separation.

- Dynamic attrset keys not tracked in recursive sets (`nameres.rs`): could cause
  incorrect SCC grouping in edge cases.

- **OOM on full nixpkgs pkgs/**: even with `-j 1`, certain files may cause
  unbounded memory growth during inference or canonicalization. The chromium/
  default.nix OOM (caused by `intern_output_ty` lacking TyRef dedup) and the
  python-packages.nix OOM (caused by `infer_expr` re-evaluating shared
  sub-expressions O(N²) times in `inherit (from) f1..fN` patterns) were fixed,
  but other pathological files may still exist.

- **~20 GB RSS on full nixpkgs** (parallel): checking all 42k files in parallel
  uses ~20 GB RAM. Most comes from parallel inference holding all files' type
  state concurrently. Limiting `-j` helps but the per-file OOM above is the
  harder problem.

- Stale analysis name lookup (`completion.rs`): `find_name_type_by_text()` returns
  first match when source_map fails, may pick wrong shadowed binding.

- No tests for chain re-analysis (A->B->C): requires full async analysis loop.

- `reload_registry` (state.rs) still uses `nix_file.contents(&self.db)` which has
  the same cross-DB salsa ID issue for warmup-merged files. Less likely to trigger
  since config reload usually happens after the user opens files (re-registering
  them in the main DB), but could panic if config is reloaded before any file is
  opened manually.

- `nix build .#stubs` emits `system.stateVersion is not set` warning.

- Home Manager flake mode (`gen-stubs home-manager --flake`) untested end-to-end.

- **Frozen union oracle mismatch**: `if true then (import /a.nix) else (import /b.nix)`
  where A is a polymorphic lambda and B is a union produces structurally different
  types via the Frozen path vs inline. Frozen: `a -> (bool | [string] | ...)`,
  inline: `(a -> bool) | [string] | ...`. Likely caused by how `intern_output_ty`
  handles TyVar from external arenas in union contexts. PBT test demoted to
  crash-freedom only for now.

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

### Type-Level Operators & Cross-File Types

- **Phase 4b (partial inference) not yet implemented**: `type Scope = typeof scope;`
  exported from one file and imported by another via `import("./path.nix").Scope`
  requires partial inference of the exporting file (just the SCC containing `scope`).
  The existing `infer_prog_partial` loop already supports early exit — need to add
  `infer_prog_up_to_group(stop_idx)` and wire it into a coordinator
  `demand_type_exports()` method with TypeExportSlot caching.

- **Coordinator integration**: The CheckCtx `imported_type_exports` and
  `typeof_import_types` fields are populated in tests but not yet by the coordinator.
  Need to wire `extract_type_exports` into `compute_file` and scan doc comments for
  cross-file type references during import resolution.

- **Diagnostics for type operator errors**: Param of non-function, Return of
  non-function, field access on non-attrset, unknown typeof name, etc. all silently
  degrade to fresh variables. Should emit proper diagnostics with E0XX codes.

### Cross-File Inference (InferenceCoordinator)

- Layered inference (`tix check`) caches file signatures between layers with
  ref-counted eviction (signatures are dropped once all importers are processed).
  This avoids the earlier OOM from accumulating 40k+ OutputTy values, but there
  is no LRU eviction for demand-inferred files in the LSP coordinator cache —
  those accumulate indefinitely.

### Remaining Optimization Opportunities

- **Lazy bounds propagation**: Don't propagate bounds through link_extruded_var
  immediately; instead record the link and propagate on demand when the fresh
  variable is actually constrained at a use site.
- **BTreeMap -> sorted Vec for output `AttrSetTy`:** Fields are built once, read-only
  after. `Vec<(SmolStr, TyRef)>` with binary search would halve allocation overhead.
  Deferred because it's invasive (~15 files across 4 crates).

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
- **`builtins.tryEval` cannot catch native Nix type errors** (e.g. attribute
  access on null). This prevents evaluating `v.default` for options whose
  defaults reference unavailable packages (like `hardware.nvidia.open`).
  The `hasDefault` heuristic + `is_set_like` inner-type check works around
  this, but a proper fix would require Nix-level improvements or a separate
  evaluation pass.
- **Inference aborted diagnostic** says what's missing but not how to fix it.
- **No workspace/multi-root LSP support.**
- **No CONTRIBUTING.md** for potential contributors.
- **No recursive type aliases** in `.tix` files.

### Excluded-but-imported files as nocheck

The `[project] excludes` currently skips files entirely from discovery. The plan also
calls for excluded files that are reached via imports (from included files) to still be
parsed/inferred with diagnostics suppressed (nocheck behavior). This "excluded-but-imported"
handling is not yet implemented — it would require detecting excluded import targets
during Phase 1b of `tix check` and flagging them as nocheck in the pipeline.

### DX Audit: What Works Well

Strengths to preserve during future work:

- Core type inference: row polymorphism, union types, narrowing, let-polymorphism.
- Stubs: clean `.tix` syntax, module->type-alias system, ~500+ lib declarations.
- LSP: 14 features including code actions, semantic tokens, signature help.
- Error messages: miette formatting, "did you mean?", source context.
- Narrowing: `builtins.isString`, `x ? field`, `x == null`, `assert`, boolean
  combinators. Catches bugs nothing else can.
- `tix.toml` context system: glob-based context assignment.
- `gen-stubs nixos --descriptions`: option descriptions in LSP hover.
- `@callpackage` context: zero-annotation types for nixpkgs packages.
