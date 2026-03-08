## Known Issues & Future Work

Items not tracked in backlog — either too small for a task, known limitations
by design, or informational notes.

### Canonicalization / Type Display

- **Let-binding loses union type**: `let x = if true then 1 else "hi"; in x`
  infers `x :: int | string` but the root expression type for `x` is just the
  first branch's type (e.g. `int`). Early canonicalization sees partial bounds
  at the reference site. Affects PBT: union-typed expressions can't be wrapped
  in `non_type_modifying_transform` (let-bind/attrset selection).

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
