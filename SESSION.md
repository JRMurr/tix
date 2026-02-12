## Known Issues & Future Work

### PBT Generator Issues (deferred)

- PBT `func_strat` `fully_known` variant: `if param == <value>` doesn't fully
  constrain the param type in SimpleSub when the value goes through variable
  intermediaries (e.g. attrset select results of overloaded operations). The `==`
  operator establishes bidirectional variable-to-variable links, and concrete types
  flow correctly as lower bounds through the chain. However, in negative position,
  canonicalization uses upper bounds, and the variable cycle has no concrete upper
  bound — only lower bounds. Added explicit concrete propagation in the `==` case
  (`find_concrete` + `alloc_concrete` + `constrain`) as a partial fix, but this only
  helps when the concrete type is available at inference time (not for deferred
  overloads). A proper fix likely requires type simplification or a different
  canonicalization strategy.

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

- PBT test (`pbt::test_type_check`) may need updating for early canonicalization — it
  was designed before this change and may produce types that differ between early and
  late canonicalization for certain generated patterns.

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
