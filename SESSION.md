## Known Issues & Future Work

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

### Missing Features

- Multi-`with` fallthrough: only the innermost `with` env is constrained for
  unresolved names. Nix semantics would check outer `with` scopes when the inner
  one lacks the attribute, but that requires runtime-like dynamic dispatch.
- `merge_attrset_intersection` field overlap: when one field is a TyVar, the other
  is preferred unconditionally rather than producing a proper intersection.

### Multi-File Imports

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

### Automatic Type Extraction from Nix Ecosystem

- **Eval-assisted stub generation for `lib`**: Use `nix eval` to discover the attrset
  structure of nixpkgs `lib`, combine with `builtins.functionArgs` to get parameter
  names, and optionally run tix inference on the lib source where feasible. Output a
  `.tix` skeleton with known types filled in and TODOs for what couldn't be inferred.
  `lib` is ~260 functions — manageable to hand-verify once generated. Could evolve
  into a general `tix-gen` tool for any Nix attrset.

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

### Future Enhancements

- Full intersection-type-based operator overloading (replace pragmatic deferred
  overload list with proper intersection types for overloaded functions)
- Type narrowing: Phase 1 (null narrowing) and Phase 2a (`?`/hasAttr, single-key
  only) are implemented. Remaining: isAttrs, isFunction, isList, primitive
  predicates, multi-key `?` paths, `&&`/`||` combinators.
- The `==` operator uses bidirectional constraints (`constrain(a,b); constrain(b,a)`),
  which means `x == null` forces x's type to include null as both a lower AND upper
  bound. This is too restrictive — equality comparison doesn't imply type equality
  (Nix allows `1 == "hi"` → false). Relaxing `==` to not add bidirectional constraints
  (or only constraining in one direction) would fix false positives in patterns like
  `hydraJob` where field access via `or` default happens before the null guard.
- Literal / singleton types (`"circle"` as a type, not just `string`)
- Type narrowing + arithmetic in narrowed branches: `x: if x == null then x else x - 1`
  produces body type `null` rather than `null | number`. The narrowed else-branch creates
  a fresh variable for x; arithmetic on that fresh variable produces a result whose
  lower bounds don't survive canonicalization in the union with null. The unconstrained
  result var in positive position is bottom, so `null | bottom = null`. This may be
  correct from the type system's perspective but is surprising. Worth investigating
  whether the arithmetic constraints should propagate lower bounds more eagerly.
- Co-occurrence simplification: path-based co-occurrence grouping is strict —
  variables that appear at structurally different positions (e.g. different attrset
  fields) won't be merged. This could be relaxed to use "occurrence signature"
  based grouping per the SimpleSub paper §4.2.
