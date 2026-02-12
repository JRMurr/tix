## Known Issues & Future Work

### PBT Generator

- PBT lambda param constraining now uses `__pbt_assert_<prim>` builtins (test-only
  identity functions with known types, e.g. `__pbt_assert_int :: int -> int`) instead
  of the old `if param == <value>` equality trick. Application contravariance reliably
  constrains param types in all cases. The old approach was unreliable in SimpleSub
  because `==` establishes bidirectional variable links without concrete upper bounds.

- PBT tests are split into focused properties: `test_primitive_typing`,
  `test_structural_typing`, `test_lambda_typing`, and `test_combined_typing` (lower
  case count for breadth).

### Number Primitive + Partial Resolution

- Within the same SCC group, multiple uses of a polymorphic function (like `apply`)
  share the same type variables. This means partial resolution constraints from one
  use site (e.g. `apply add 2` adds Number bounds) contaminate other use sites
  (e.g. `apply (x: x + "hi") "foo"` also shows `number -> number` instead of `string`).
  Per-use instantiation within SCC groups would fix this but isn't currently implemented.

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

- `with` expression support
- `StringInterpolation` and `PathInterpolation` expression support
- Dynamic attrset fields in Select expressions
- Proper intersection of field types in `merge_attrset_intersection` (currently
  takes the non-TyVar one)
- `dyn_ty` merging in attrset intersection
- Reference substitution in type annotations (`TypeVarValue::Reference`)
- AttrSet type annotations in comment parser

### Future Enhancements

- Full intersection-type-based operator overloading (replace pragmatic deferred
  overload list with proper intersection types for overloaded functions)
- Type narrowing / flow-sensitive typing (TypeScript-style discriminated unions)
- Literal / singleton types (`"circle"` as a type, not just `string`)
- Co-occurrence simplification (`lang_ty::simplify`) currently handles polar-only
  variable removal and has scaffolding for co-occurrence merging, but the path-based
  co-occurrence grouping is strict — variables that appear at structurally different
  positions (e.g. different attrset fields) won't be merged. This could be relaxed
  to use "occurrence signature" based grouping per the SimpleSub paper §4.2.
