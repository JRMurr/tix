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

- Polymorphic types like `apply = fn: args: fn args` show use-site contamination in
  their canonical type (e.g. `((int | string) -> a) -> b -> ...` instead of
  `(a -> b) -> a -> b`). This is correct un-simplified SimpleSub behavior: when a
  polymorphic type is extruded at a use site, fresh variables are linked back to
  originals via bounds, and use-site constraints flow back. The canonicalization then
  follows these bounds to the contaminated originals. Type simplification (Section 4.2
  / co-occurrence analysis) would merge co-occurring variables and clean this up.

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
- Type simplification via co-occurrence analysis and variable merging
  (Parreaux Section 5)
