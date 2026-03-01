## Known Issues & Future Work

### Merge Constraints Not Carried Across SCC Groups

Polymorphic `//` merge constraints are discarded at SCC group end (only overloads
are carried). This means `let f = a: b: (a // b).z; in f { x = 1; } { y = 2; }`
does NOT error — the merge never resolves because neither operand becomes concrete
within the SCC group. PendingHasField can't fix this because the merge result
never becomes concrete within the group. Fixing this would require carrying merge
constraints (similar to how overloads are carried) and re-instantiating them during
extrusion.

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

### CLI Display of Narrowed Lambda Types

- RESOLVED: The CLI correctly displays narrowed lambda types (e.g.
  `x: if isNull x then 0 else x` → `a -> int | ~null`). The earlier
  observation of `a` was caused by a race condition in `scripts/tixc.sh`
  where the temp file could be deleted before the binary finished reading it.

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
  - `nameFromURL :: String -> String` annotation (line 2101): wrong arity
    (1 arg, function takes 2). Detected and skipped with a warning.
  - Previously fixed: `hasSuffix`/`hasPrefix`/`hasInfix` warnIf errors resolved
    by per-val generic scoping in module stubs + pre-applying entry Lambda
    annotations before SCC groups + lifting stub-level variables for extrusion.
    `lib.pipe` in `sanitizeDerivationName` error resolved by the same fix
    (stub polymorphic instantiation). `getName`/`getVersion` errors resolved
    by locally-aliased builtin narrowing. `nameFromURL` body error resolved
    by annotation arity check preventing type table corruption.

### Missing Features

- `true`, `false`, `null` keywords inside `with` bodies are resolved as
  `WithExprs(...)` instead of falling through to the special-case handler in
  `infer_reference`. Name resolution doesn't treat them as builtins, so they
  enter the `with` lookup path. Single `with` works because the env attrset
  typically doesn't have a `true` field and the open constraint passes, but
  nested `with` with a closed outer env can produce spurious MissingField errors.
  Fix: either add `true`/`false`/`null` to `GLOBAL_BUILTIN_NAMES` in nameres, or
  check for them before the `WithExprs` path in `infer_reference`.
- `merge_attrset_intersection` field overlap: when one field is a TyVar, the other
  is preferred unconditionally rather than producing a proper intersection.

### Multi-File Imports

- Angle bracket search paths (`<nixpkgs>`) are silently skipped during import
  resolution. They need NIX_PATH lookup to resolve properly — tracked as a TODO
  in `imports.rs`.

- Deferred overloads (e.g. `+` in `a: b: a + b`) don't survive the OutputTy
  boundary between files. When file A imports file B that exports an overloaded
  function, the overload context is lost — the exported type has free type vars
  instead of concrete types. Subtraction/multiplication/division work because
  they constrain operands to Number immediately, but `+` (valid for strings/paths
  too) remains fully polymorphic. A fix would require either carrying overload
  metadata in OutputTy or resolving all overloads before export.

- Cyclic imports degrade gracefully (unconstrained type variable + diagnostic)
  but don't support cross-file mutual recursion. A future extension could merge
  cyclic file modules into a combined module for joint SCC inference.

### Unconstrained Variables Cause Pathological Constraint Propagation

- Files with heavily-used variables like `pkgs` and `lib` that lack type
  annotations suffer exponential constraint propagation. Without `/** type:
  lib :: Lib */`, every `lib.foo` access adds a field bound to the variable.
  By SCC group 50, the bounds graph is so interconnected that a single
  `constrain()` call cascades through 18M+ operations. Adding type annotations
  reduces inference from 80 seconds to 400ms. The deadline mechanism (5s for
  imports, 10s for top-level) acts as a safety net but the real fix is stubs.

### LSP Auto-Completion

- Lambda parameter completion is limited: when typing `pkgs.` inside a lambda
  body, the parameter's type is only known from within-body constraints (other
  field accesses on the same variable). Call-site argument types don't flow back
  to the original parameter variable due to SimpleSub's extrusion-based
  generalization. Full call-site analysis or type annotations/stubs are needed
  for comprehensive completion on function parameters.

- rnix error recovery on incomplete code (e.g. `pkgs.` with no field name) can
  cascade: the missing field causes surrounding tokens to be consumed as part of
  the Select's attrpath, mangling subsequent expressions. This can destroy call
  sites that would otherwise constrain lambda parameters.

### LSP Hover on Multi-Element Attrpaths

- rnix parses `a.foo.bar` as a single Select with a two-element attrpath, not
  nested Selects. Hovering on any element (`foo` or `bar`) skips to the same
  Select node and shows the overall result type (`int`), rather than the
  intermediate type (`{ bar: int }` for `foo`). Fixing this would require
  mapping individual attrpath elements back to their corresponding intermediate
  ExprIds from the Tix AST lowering (which does produce nested Selects).

### LSP Inlay Hints & NameKind Classification

- Files wrapped in a top-level lambda with `{ pkgs ? <nixpkgs> }:` produce
  `PlainAttrset` NameKind for the inner let-binding names (because the result
  is an attrset `{ inherit add ...; }`). The actual LetIn-scoped NameIds are
  separate but get the wrong kind. Inlay hints now handle `PlainAttrset` names
  with non-trivial bindings, but the underlying `lang_ast` lowering could be
  investigated to ensure NameKind classification is correct for let bindings
  inside top-level lambda bodies.

### Stub Audit: Remaining Generator Issues (nixos.tix / home-manager.tix)

The following issues were identified in an audit but not yet fixed:

**nixos.tix / home-manager.tix generator (`tools/extract-options.nix`):**
- `tryEval` failures silently degrade types to `{ ... }` — affects common
  options like `networking.firewall.allowedTCPPorts` (should be `[int]`),
  `boot.kernelParams` (should be `[string]`), and 593 `enable` fields.
- 92 redundant `{ ... } | { ... }` unions should be deduplicated.
- `specialisation` embeds ~90k lines of recursive NixOS config inline instead
  of referencing `NixosConfig`.
- Submodule indent resets to 0 inside `AttrsOf` (cosmetic).

**Parameterized type aliases (future feature):**
- `type Overridable<T> = T | T -> T` would reduce duplication in stubs.
  Requires grammar changes, `TypeApplication` ParsedTy variant, substitution
  engine, and arity checking. The current implicit generic system works but
  doesn't support applying aliases to specific type arguments.

### Automatic Type Extraction from Nix Ecosystem

- **Lib stubs are now generated from noogle data**: `scripts/gen_lib_stubs.py` pulls
  structured data from `nix build 'github:nix-community/noogle#data-json'` and
  translates ~500 type signatures into `.tix` declarations. ~200 lib functions lack
  noogle signatures and are omitted. Could supplement with `nix eval` + `functionArgs`
  to discover parameter names for those.

- **Generated stubs are now part of the Nix build**: `nix build .#stubs` and
  `nix build .#with-stubs` generate NixOS/HM stubs at build time. The evaluation
  emits a `system.stateVersion is not set` warning — could be suppressed by
  setting a dummy stateVersion in the eval-config module list.

- **Home Manager flake mode**: The `gen-stubs home-manager --flake` path evaluates
  `homeConfigurations` but hasn't been tested end-to-end with real flakes yet.
  The non-flake mode (fetching HM from flake registry) works.

### tower-lsp Transport Crash

- Editing files in VS Code can trigger `unreachable!()` at
  `tower-lsp-0.20.0/src/transport.rs:120`. This is inside tower-lsp's message
  transport, not our code. May be a known upstream issue. Investigate whether
  upgrading tower-lsp or switching to a different LSP framework resolves it.

### Stub Generator: Namespace-Level Doc Comments

- Generated stubs only have `##` doc comments on leaf options (e.g.
  `programs.steam.enable`), not on intermediate namespace fields (e.g.
  `programs.steam`). This means completing `programs.` shows no docs for
  most entries. Could hoist the `enable` option's description up to the
  parent namespace, or synthesize a summary from child options.

### Stubs `Any` Type Alias

- The `.tix` stub type alias `Any` is currently interned as a fresh
  unconstrained type variable (`new_var()`) rather than `OutputTy::Top`.
  Each `Any` reference creates an independent variable, which is pragmatically
  correct but displays as a bare type variable (`a`) instead of `any`.
  Adding `Ty::Top` to the inference-time representation would fix this but
  requires updates to `constrain.rs`. Low priority — the fresh-variable
  approach gives correct inference behavior.

### Null-Default Field: Polymorphic Return Type Loses Default

- `let f = { config ? null }: config; in f {}` returns a free type variable
  instead of `null`. After generalization, the null lower bound from the default
  doesn't surface at call sites that omit the field. Contrast with the inline
  (monomorphic) call `({ config ? null }: config) {}` which correctly returns
  `null`. Similarly, the canonical type of `f` displays as `{ config?: a } -> null`
  rather than `{ config?: a } -> (a | null)` — the return-position expansion
  of the variable shows only the lower bound (null) without the type variable.
  Likely an interaction between optional-field default handling and extrusion.

### `test/null_default.nix` Residual Error

- After the SCC narrowing pre-pass fix, the `pasta != null` + let-binding patterns
  in `null_default.nix` type-check correctly. However, line 45 still errors:
  `lib.findFirst (k: arg ? ${k}) null (builtins.attrNames bindTypes)` — the `null`
  literal as `findFirst`'s default arg causes a `string vs null` mismatch because
  `findFirst` is not stubbed. Unrelated to narrowing.

### `infer_expr_inner` Expr Clone

- `infer_expr_inner` clones the entire Expr enum from `self.module[e]` to release
  the borrow on `self.module` before calling `&mut self` methods. This is required
  by Rust's borrow checker but could be avoided by matching on `&Expr` and collecting
  needed data into local Copy variables. The refactor is non-trivial because some arms
  (StringInterpolation) re-reference the original `expr`. Low priority — the clone
  cost is dominated by Bindings/Pat variants which are infrequent in typical code.

### Known Performance Characteristics

The following O(n^2) patterns are intentional trade-offs, acceptable for typical
Nix code sizes (hundreds of bindings per file, not millions):

- **Deferred overload re-instantiation** (`infer.rs:257-261`): fixed-point loop
  over carried overloads during extrusion. Each pass is O(carried.len()), and
  the number of passes is bounded by the overload chain depth (typically 1-3).
- **Attrset subsumption** (`collect.rs:457-514`): pairwise comparison of attrset
  types in union simplification. k (number of attrset members) is small in
  practice.
- **Pending constraint resolution** (`infer.rs:488-545`): swap-and-filter loop
  over pending constraints. Each pass processes the whole list; bounded by the
  number of resolution steps (typically converges in 2-3 passes).
- **Conservative union routing** (`constrain.rs:429-434`): when both union
  members are variables, constraints are routed to both. Sound but may create
  unnecessary bounds.

### Future Enhancements

- Full intersection-type-based operator overloading (replace pragmatic deferred
  overload list with proper intersection types for overloaded functions)
- Literal / singleton types (`"circle"` as a type, not just `string`)
- Multi-key `?` attrpath narrowing (only single keys are currently supported)
- Else-branch narrowing for compound types (`isAttrs`/`isList`/`isFunction`
  only narrow the then-branch; else-branch is skipped because `¬{..}` etc.
  are not representable)
- Co-occurrence simplification: path-based co-occurrence grouping is strict —
  variables that appear at structurally different positions (e.g. different attrset
  fields) won't be merged. This could be relaxed to use "occurrence signature"
  based grouping per the SimpleSub paper §4.2.

### Recursive Function Narrowing Conflicts (modules.nix, generators.nix)

- Recursive functions with `isFunction`/`isAttrs`/`isList` narrowing on the
  same parameter produce false positives (3 errors in modules.nix:423, 2-3 in
  generators.nix). Root cause: SCC-level inference shares a single type variable
  for the parameter across all call sites, including recursive calls from other
  branches. E.g. in `loadModule`:
  ```
  if isFunction m then ... m args ...
  else if isAttrs m then loadModule ... { config = m; }
  ```
  The recursive call constrains `m` to accept attrsets, conflicting with the
  function narrowing in the then-branch. Fix requires per-call-site flow
  sensitivity, which is beyond the current SCC architecture.

### `||` Short-Circuit Narrowing: Chained Null Guards

- `elemType == null || lazy == null || placeholder == null` (types.nix:838)
  produces a `~null` vs `null` error in the rightmost operand. Left-assoc `||`
  applies else-branch narrowing from the compound LHS to the RHS, making
  `placeholder` narrowed to `~null` from the outer `||`. The comparison
  `placeholder == null` succeeds (== is total) but downstream code that expects
  `placeholder` to potentially be null sees `~null`. Partial fix — most `||`
  patterns work, but chained null guards on 3+ variables can surface this.

### LSP Blocks on Large Repos (Serial didOpen Processing)

- PARTIALLY RESOLVED: All 6 phases of the Salsa concurrency migration are complete.
  Handlers now read from a lock-free DashMap<PathBuf, FileSnapshot> instead of
  locking the AnalysisState mutex. The analysis loop holds the mutex only during
  the fast syntax phase (~5-50ms) and writes snapshots immediately, so handlers
  are responsive even during type inference. Completion uses a single unified
  codepath with name-text fallbacks for all strategies when source_map fails
  (stale analysis). Cancel flag simplified from `Arc<Mutex<Arc<AtomicBool>>>`
  to a single shared `Arc<AtomicBool>`. Parse results cached in RootDatabase
  (DashMap) so repeated parse_file calls don't re-parse.
  - Import resolution now uses Salsa-memoized `file_root_type` (via `StubConfig`
    input) so previously-inferred imports return instantly on subsequent loads.
    Aggregate deadline (30s) bounds the total import tree wall-clock time.
    Canonicalization respects deadline to prevent 7s→11s overshoot.
  - Legacy import inference path removed — always uses Salsa `file_root_type`.
  - `update_syntax` split into Phase A (parse/nameres, ~5-50ms mutex) and
    Phase B (import resolution, mutex re-acquired). Handlers are responsive
    between phases.
  - Side-channel import limits on RootDatabase (aggregate deadline, cancel flag,
    max imports) allow the Salsa path to respect the same caps without
    invalidating cached results.
  - Parallel import inference via rayon for files with 50+ imports: BFS
    discovery of the import graph, then topological sort + `par_iter` at each
    level. Bypasses Salsa memoization — results stored in HashMap. Sequential
    Salsa path remains primary for incremental single-file updates.
  - Canonicalization deadline (checked every 512 ops) prevents degenerate type
    graphs from hanging the canonicalization phase.
  - Remaining cleanup:
    - Legacy `pending_text` / `state.files` still exist alongside DashMap snapshots
    - hover/completion still lock state briefly for DocIndex (should store separately)
    - goto_def/rename cross-file still lock state for Salsa DB access
    - Regression tests for import cap, aggregate deadline, canonicalization
      deadline, and cancel flag in Salsa path are not yet written.

### `contains_union()` Doesn't See Through Alias References

- When a type annotation references a type alias that contains a union
  (e.g. `type: x :: Nullable` where `Nullable = int | null`), the
  `contains_union()` safety check operates on the top-level `ParsedTy` which
  is `TyVar(Reference("Nullable"))` — not the expanded alias body. So the
  union check doesn't trigger, and the annotation is applied with bidirectional
  constraints, which can produce false type errors (e.g. `null` vs `int`).
  Fix: expand alias references before checking `contains_union()`, or check
  after interning.

### Docs: No Dedicated Diagnostics Reference Page

- The LSP and CLI produce several diagnostic kinds (TypeMismatch, MissingField,
  DuplicateKey, etc.) but there's no docs page listing all diagnostics, their
  severity, and what triggers them. Low priority since the messages are self-
  explanatory, but a reference page would be useful.

### `resolve_to_concrete_id` Picks Arbitrary Lower Bound

- `resolve_to_concrete_id` follows the first reachable lower bound to find a
  concrete type. For variables with multiple distinct concrete lower bounds
  (e.g. `null | int`), it picks one arbitrarily. This is used in poly_type_env
  recording and early canonicalization. The narrowing fix (using
  `ty_for_name_direct` instead of `name_slot_or_override`) works around this
  for the narrowing case, but the underlying issue could cause other subtle
  problems if poly_type_env entries are expected to represent the full type.

### Code Review: Deferred Low-Priority Items

- **LSP `LineIndex` assumes ASCII** (`lsp/src/convert.rs`): character offset ==
  byte offset. Files with multi-byte UTF-8 in comments/strings get misaligned
  hover/completion after the first non-ASCII character. Fix requires UTF-16 offset
  counting per the LSP spec.

- **`collect.rs` is ~1756 lines** with intertwined canonicalization and normalization.
  Could benefit from phase separation (canonicalize, then normalize as a separate pass).

- **`BindingValueKind::ImplicitSet`** (`lower.rs:354`) is never constructed.
  Dead code — `#[allow(dead_code)]` is already present. Could be removed or implemented.

- **Dynamic attrset keys not tracked in recursive sets** (`nameres.rs:333-335`):
  `rec { "${x}_key" = expr; x = ...; }` — dependency on `x` in the dynamic key
  isn't recorded. Could cause incorrect SCC grouping in edge cases.

- **Narrowing silently produces no result on complex attrpaths** (`narrow.rs:453`):
  `single_static_attrpath_key()` returns `None` for multi-segment paths. Narrowing
  stops working on `x.a.b ? "default"` patterns with no indication why.

- **Hardcoded conditional function list for narrowing** (`narrow.rs:89-97`):
  `ConditionalFn` enum is hardcoded. Adding new library functions with narrowing
  semantics requires code changes. Could be data-driven via `.tix` stub annotations.

- **Extrude carried-overload loop is O(n^2)** (`infer.rs:383-441`): re-scans all
  carried overloads on each iteration. Linear with a worklist approach. Only matters
  for deeply chained expressions like `a + b + c + ... + z`.

- **Stale analysis name lookup may pick wrong shadowed binding**
  (`completion.rs:281-283`): `find_name_type_by_text()` returns first match when
  source_map fails, which may be wrong with shadowing.

- **No tests for chain re-analysis (A→B→C)**: The dependency tracking
  methods (`record_import_deps`, `update_ephemeral_stub`, etc.) now have unit
  tests for the basic scenarios. However, transitive chain re-analysis (C changes
  → both A and B re-analyzed) isn't tested because it requires the full analysis
  loop in `server.rs`, which is async and harder to test in isolation.

### Doc Comment Collection Panics (collect.rs) — RESOLVED

- Converted all `unreachable!()`/`unwrap()` calls in both `collect.rs` and
  `tix_collect.rs` to proper `Result<_, CollectError>` returns. Both doc comment
  and `.tix` file collection now surface clean error messages instead of panics.

### LSP Duplicate Key Diagnostic — RESOLVED

- Added `DiagnosticRelatedInformation` pointing to the first definition when
  reporting duplicate keys. Users can now navigate to the first definition
  directly from the diagnostic.

### Timeout Diagnostic Per-Binding Detail — RESOLVED

- `InferenceTimeout` now carries `missing_bindings: Vec<SmolStr>` identifying
  which bindings were not inferred before the deadline. The diagnostic message
  lists them (truncated to 5 with "and N more" for large counts).
