## Known Issues & Future Work

### Merge Constraints Not Carried Across SCC Groups

Polymorphic `//` merge constraints are discarded at SCC group end (only overloads
are carried). This means `let f = a: b: (a // b).z; in f { x = 1; } { y = 2; }`
does NOT error — the merge never resolves because neither operand becomes concrete
within the SCC group. Fixing requires carrying merge constraints (similar to
overloads) and re-instantiating them during extrusion.

### Intersection Annotation Body Verification

- Per-component verification of intersection-of-function annotations is deferred.
  Currently, `(int -> int) & (string -> string)` is accepted as a declared type
  (store-and-trust), but the body is not checked against each component separately.
  Full verification would require either re-inferring the body once per component
  or adding a check-mode to the inference engine.

### Overload Resolution + Extrusion

- `find_pinned_concrete`: a targeted fix for variables that were fully resolved by
  overload resolution but are still stored as Variables. Only handles primitives
  to avoid incorrectly short-circuiting polymorphic types with structural bounds
  (like open attrsets). A more principled fix would be to either (a) replace the
  Variable entry with a Concrete entry when overload resolution pins a var, or
  (b) improve extrusion to propagate both lower and upper bounds for resolved vars.

- The deferred overload approach adds significant complexity to extrusion (fixed-point
  loop for re-instantiation, interaction with constraint cache). Consider replacing
  with intersection-type-based overloading (see Future Enhancements).

### Canonicalization / Type Display

- Early canonicalization captures clean polymorphic types for name bindings, but the
  root expression type (the final attrset in `test/basic.nix`) still shows contaminated
  types for inherited names. The inherit creates a new NameId whose type comes from
  extruding the original, and that extruded reference picks up use-site bounds. A full
  fix would propagate early-canonical types through expression-level canonicalization.

- The upper-bound fallback in canonicalization (variables with only primitive upper
  bounds display as that primitive in positive position) may be too aggressive in
  some edge cases. Monitor for false positives in PBT.

### Builtin Types

- Deferred builtins (arithmetic `add`/`sub`/`mul`/`div`, `baseNameOf`/`dirOf`,
  `derivation`, `genericClosure`, fetch functions) return fresh type variables
  because they need type system extensions (`number` union, `stringish` union,
  complex structural types). They won't cause errors but provide no type info.

- The `builtins` attrset is synthesized fresh on every reference to the name
  `"builtins"`. This is correct but potentially expensive if `builtins` is
  referenced many times. Could cache the attrset structure and extrude it.

- `test/strings.nix` has 0 errors + 1 annotation warning:
  `nameFromURL :: String -> String` (line 2101): wrong arity (1 arg, function
  takes 2). Detected and skipped with a warning.

### Multi-File Imports

- Angle bracket search paths (`<nixpkgs>`) are silently skipped during import
  resolution. They need NIX_PATH lookup to resolve properly — tracked as a TODO
  in `imports.rs`.

- Deferred overloads (e.g. `+` in `a: b: a + b`) don't survive the OutputTy
  boundary between files. When file A imports file B that exports an overloaded
  function, the overload context is lost — the exported type has free type vars
  instead of concrete types. A fix would require either carrying overload
  metadata in OutputTy or resolving all overloads before export.

- Cyclic imports degrade gracefully (unconstrained type variable + diagnostic)
  but don't support cross-file mutual recursion.

### Unconstrained Variables Cause Pathological Constraint Propagation

- Files with heavily-used variables like `pkgs` and `lib` that lack type
  annotations suffer exponential constraint propagation. The deadline mechanism
  (5s for imports, 10s for top-level) acts as a safety net but the real fix is
  stubs/annotations.

### LSP Auto-Completion

- Lambda parameter completion is limited: when typing `pkgs.` inside a lambda
  body, the parameter's type is only known from within-body constraints (other
  field accesses on the same variable). Call-site argument types don't flow back
  to the original parameter variable due to SimpleSub's extrusion-based
  generalization. Full call-site analysis or type annotations/stubs are needed
  for comprehensive completion on function parameters.

- rnix error recovery on incomplete code (e.g. `pkgs.` with no field name) can
  cascade: the missing field causes surrounding tokens to be consumed as part of
  the Select's attrpath, mangling subsequent expressions.

### LSP Hover on Multi-Element Attrpaths

- rnix parses `a.foo.bar` as a single Select with a two-element attrpath, not
  nested Selects. Hovering on any element shows the overall result type rather
  than the intermediate type. Fixing requires mapping individual attrpath
  elements back to their corresponding intermediate ExprIds from the Tix AST
  lowering (which does produce nested Selects).

### LSP Inlay Hints & NameKind Classification

- Files wrapped in a top-level lambda with `{ pkgs ? <nixpkgs> }:` produce
  `PlainAttrset` NameKind for the inner let-binding names. Inlay hints now
  handle `PlainAttrset` names with non-trivial bindings, but the underlying
  `lang_ast` lowering could be investigated to ensure NameKind classification
  is correct for let bindings inside top-level lambda bodies.

### Stub Audit: Remaining Generator Issues (nixos.tix / home-manager.tix)

**nixos.tix / home-manager.tix generator (`tools/extract-options.nix`):**
- `tryEval` failures silently degrade types to `{ ... }` — affects common
  options like `networking.firewall.allowedTCPPorts` (should be `[int]`),
  `boot.kernelParams` (should be `[string]`), and 593 `enable` fields.
- 92 redundant `{ ... } | { ... }` unions should be deduplicated.
- `specialisation` embeds ~90k lines of recursive NixOS config inline instead
  of referencing `NixosConfig`.

**Parameterized type aliases (future feature):**
- `type Overridable<T> = T | T -> T` would reduce duplication in stubs.
  Requires grammar changes, `TypeApplication` ParsedTy variant, substitution
  engine, and arity checking.

### Automatic Type Extraction from Nix Ecosystem

- ~200 lib functions lack noogle signatures and are omitted from generated stubs.
  Could supplement with `nix eval` + `functionArgs` for parameter names.

- `nix build .#stubs` emits a `system.stateVersion is not set` warning — could
  be suppressed by setting a dummy stateVersion in the eval-config module list.

- Home Manager flake mode (`gen-stubs home-manager --flake`) evaluates
  `homeConfigurations` but hasn't been tested end-to-end with real flakes yet.

### tower-lsp Transport Crash

- Editing files in VS Code can trigger `unreachable!()` at
  `tower-lsp-0.20.0/src/transport.rs:120`. This is inside tower-lsp's message
  transport, not our code. Investigate whether upgrading tower-lsp or switching
  to a different LSP framework resolves it.

### Stub Generator: Namespace-Level Doc Comments

- Generated stubs only have `##` doc comments on leaf options, not on
  intermediate namespace fields. Completing `programs.` shows no docs for
  most entries. Could hoist `enable` descriptions up to the parent namespace.

### Stubs `Any` Type Alias

- `Any` is interned as a fresh unconstrained type variable (`new_var()`) rather
  than `OutputTy::Top`. Displays as a bare type variable (`a`) instead of `any`.
  Adding `Ty::Top` to the inference-time representation would fix this but
  requires updates to `constrain.rs`. Low priority — correct inference behavior.

### Null-Default Field: Polymorphic Return Type Loses Default

- `let f = { config ? null }: config; in f {}` returns a free type variable
  instead of `null`. The canonical type displays as `{ config?: a } -> null`
  rather than `{ config?: a } -> (a | null)`. Likely an interaction between
  optional-field default handling and extrusion.

### `test/null_default.nix` Residual Error

- Line 45 still errors: `lib.findFirst (k: arg ? ${k}) null ...` — the `null`
  literal as `findFirst`'s default arg causes a `string vs null` mismatch
  because `findFirst` is not stubbed. Unrelated to narrowing.

### `infer_expr_inner` Expr Clone

- `infer_expr_inner` clones the entire Expr enum to release the borrow on
  `self.module` before calling `&mut self` methods. Could be avoided by matching
  on `&Expr` and collecting needed data into local Copy variables. Low priority —
  the clone cost is dominated by Bindings/Pat variants which are infrequent.

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

### Future Enhancements

- Full intersection-type-based operator overloading
- Literal / singleton types (`"circle"` as a type, not just `string`)
- Multi-key `?` attrpath narrowing (only single keys currently supported)
- Else-branch narrowing for compound types (`isAttrs`/`isList`/`isFunction`)
- Co-occurrence simplification: relax to "occurrence signature" grouping per
  SimpleSub paper §4.2

### Recursive Function Narrowing Conflicts (modules.nix, generators.nix)

- Recursive functions with `isFunction`/`isAttrs`/`isList` narrowing on the
  same parameter produce false positives. Root cause: SCC-level inference shares
  a single type variable for the parameter across all call sites, including
  recursive calls from other branches. Fix requires per-call-site flow
  sensitivity, which is beyond the current SCC architecture.

### `||` Short-Circuit Narrowing: Chained Null Guards

- `a == null || b == null || c == null` produces a `~null` vs `null` error in
  the rightmost operand. Left-assoc `||` applies else-branch narrowing from the
  compound LHS to the RHS. Most `||` patterns work, but chained null guards on
  3+ variables can surface this.

### LSP Concurrency: Remaining Cleanup

The Salsa concurrency migration is structurally complete (DashMap snapshots,
split Phase A/B mutex, cancel flag, parallel rayon imports). Remaining cleanup:

- Legacy `pending_text` / `state.files` still exist alongside DashMap snapshots
- hover/completion still lock state briefly for DocIndex (should store separately)
- goto_def/rename cross-file still lock state for Salsa DB access
- Regression tests for import cap, aggregate deadline, canonicalization deadline,
  and cancel flag in Salsa path are not yet written.

### `resolve_to_concrete_id` Picks Arbitrary Lower Bound

- For variables with multiple distinct concrete lower bounds (e.g. `null | int`),
  `resolve_to_concrete_id` picks one arbitrarily. Used in poly_type_env recording
  and early canonicalization. Could cause subtle problems if poly_type_env entries
  are expected to represent the full type.

### Code Review: Deferred Low-Priority Items

- **LSP `LineIndex` assumes ASCII** (`lsp/src/convert.rs`): multi-byte UTF-8
  characters cause misaligned hover/completion. Fix requires UTF-16 offset counting.
- **`collect.rs` is ~1756 lines**: could benefit from phase separation.
- **`BindingValueKind::ImplicitSet`** (`lower.rs`): never constructed, dead code.
- **Dynamic attrset keys not tracked in recursive sets** (`nameres.rs`): could
  cause incorrect SCC grouping in edge cases.
- **Narrowing silently fails on complex attrpaths** (`narrow.rs`):
  `single_static_attrpath_key()` returns `None` for multi-segment paths.
- **Extrude carried-overload loop is O(n^2)** (`infer.rs`): could be linear
  with a worklist approach.
- **Stale analysis name lookup may pick wrong shadowed binding** (`completion.rs`):
  `find_name_type_by_text()` returns first match when source_map fails.
- **No tests for chain re-analysis (A→B→C)**: transitive import chain re-analysis
  isn't tested because it requires the full async analysis loop.
- **`tix_collect.rs` test panics**: all 29 `panic!()` calls are inside
  `#[cfg(test)]` — production code already uses `Result<_, CollectError>`.
  The `.expect()` calls at lines 320/340 are safe (length-checked `.pop()`).
