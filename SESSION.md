## Known Issues & Future Work

### PBT Generator Issues (deferred)

- `wrap_in_let` identity variant (`let id = a: a; in id(val)`) loses type information
  when `val` contains overloaded operations. Root cause: SCC grouping includes ALL
  names (even let-in names), so the identity function gets let-generalized. During
  extrusion, fresh vars inherit only lower bounds in positive polarity, and the
  resolved overload type (e.g. Int) doesn't propagate as an upper bound to the
  fresh var. Fix: either exclude let-in names from SCC grouping, or improve how
  resolved overload types propagate through extrusion.

- PBT `func_strat` `fully_known` variant: `if param == <value>` doesn't fully
  constrain the param type in SimpleSub when the value has non-primitive types
  (e.g. lambdas). In negative position, canonicalization uses upper bounds, but the
  equality constraint may only establish lower bounds for nested sub-components.
  Filtered out in PBT for now.

- Union deduplication: if-then-else with identical branches can produce spurious
  unions when the branch type contains lambda params that get different TyVar IDs
  during canonicalization. The lambdas look structurally identical but have different
  internal var numbering.

### Overload Resolution + Extrusion

- `find_pinned_concrete`: a targeted fix for variables that were fully resolved by
  overload resolution but are still stored as Variables. Only handles primitives
  to avoid incorrectly short-circuiting polymorphic types with structural bounds
  (like open attrsets). A more principled fix would be to either (a) replace the
  Variable entry with a Concrete entry when overload resolution pins a var, or
  (b) improve extrusion to propagate both lower and upper bounds for resolved vars.

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
