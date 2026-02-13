## Known Issues & Future Work

### Number Primitive + Partial Resolution

- The `Number` primitive is synthetic — it doesn't correspond to a real Nix type.
  The comment parser doesn't recognize `number` in type annotations yet (deferred).

- The upper-bound fallback in canonicalization (variables with only primitive upper
  bounds display as that primitive in positive position) may be too aggressive in
  some edge cases. Monitor for false positives in PBT.

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

### Builtin Types

- Deferred builtins (arithmetic `add`/`sub`/`mul`/`div`, `baseNameOf`/`dirOf`,
  `derivation`, `genericClosure`, fetch functions) return fresh type variables
  because they need type system extensions (`number` union, `stringish` union,
  complex structural types). They won't cause errors but provide no type info.

- The `builtins` attrset is synthesized fresh on every reference to the name
  `"builtins"`. This is correct but potentially expensive if `builtins` is
  referenced many times. Could cache the attrset structure and extrude it.

### Missing Features

- Dynamic bindings in name resolution: `nameres.rs:390` has a `todo!()` for
  traversing dynamic attrset bindings (`${expr} = value`). Files using dynamic
  keys will panic during name resolution.
- Dynamic intermediate keys in nested attr paths (`${expr}.b = 1`) are not
  desugared yet — a `todo!()` remains in `merge_nested_attr_value`.
- Multi-`with` fallthrough: only the innermost `with` env is constrained for
  unresolved names. Nix semantics would check outer `with` scopes when the inner
  one lacks the attribute, but that requires runtime-like dynamic dispatch.
- Dynamic attrset fields in Select expressions
- `merge_attrset_intersection` field overlap: when one field is a TyVar, the other
  is preferred unconditionally rather than producing a proper intersection.
- Reference substitution in type annotations (`TypeVarValue::Reference`)
- AttrSet type annotations in comment parser

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

### Future Enhancements

- Full intersection-type-based operator overloading (replace pragmatic deferred
  overload list with proper intersection types for overloaded functions)
- Type narrowing / flow-sensitive typing (TypeScript-style discriminated unions)
- Literal / singleton types (`"circle"` as a type, not just `string`)
- Co-occurrence simplification: path-based co-occurrence grouping is strict —
  variables that appear at structurally different positions (e.g. different attrset
  fields) won't be merged. This could be relaxed to use "occurrence signature"
  based grouping per the SimpleSub paper §4.2.
