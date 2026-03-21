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

- **`//` merge errors on cross-file types**: E004 "both sides must be attrsets"
  fires on patterns like `ffmpeg-base.meta // { ... }` where the LHS type comes
  from a callPackage/import that doesn't resolve to a concrete AttrSet during
  deferred merge resolution. The diagnostic renders resolved bounds (showing both
  sides as attrsets), but at resolution time the types are still variables.

- **`int + int` produces `InvalidBinOp` in isolated warmup context**: When running
  inference via `run_inference()` on `let b = import ./b.nix; in b + 1` where b.nix
  evaluates to `42`, the `+` operator produces a spurious `InvalidBinOp` diagnostic
  with both operands typed as `int`. May be related to overload resolution seeing
  the import's type after coordinator lookup vs direct inference.

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

- `nix build .#stubs` emits `system.stateVersion is not set` warning.

- Home Manager flake mode (`gen-stubs home-manager --flake`) untested end-to-end.

### PBT Flakiness

`test_combined_typing` can produce non-deterministic failures where two independent
unconstrained lambda params get the same or different TyVar indices depending on
HashMap iteration order. The test doesn't call `normalize_vars` on the actual result,
so it's sensitive to exact TyVar numbering from inference. Regression seeds are saved
in `proptest-regressions/pbt/mod.txt` but may not reproduce reliably.

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

### Cross-File Inference (InferenceCoordinator)

- **Batch mode skips signature caching** (OOM fix): `tix check` no longer
  stores root OutputTy in the coordinator during parallel inference. Accumulating
  40k+ OutputTy values caused OOM. Opportunistic cross-file resolution is
  disabled until memory-budgeted caching is implemented (e.g., LRU eviction,
  size-capped entries, or only caching types for files that are imported).
- TODO: Demand-inferred files accumulate in the coordinator cache indefinitely.
  Add LRU eviction for memory-constrained environments.

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
- **Inference aborted diagnostic** says what's missing but not how to fix it.
- **No workspace/multi-root LSP support.**
- **No CONTRIBUTING.md** for potential contributors.
- **No recursive type aliases** in `.tix` files.

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
