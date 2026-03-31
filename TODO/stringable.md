# Add `Stringable` synthetic primitive type

## Problem

String interpolation (`"${expr}"`) infers sub-expressions but doesn't constrain their types (`infer_expr.rs:498-499`). This means in code like:

```nix
bar = { name ? null }: if name != null then "hello ${name}" else "No name";
```

`bar` infers as `{ name?: null } -> string` instead of `{ name?: stringable | null } -> string`. The interpolation usage of `name` provides no type information because no constraint is emitted.

## Approach

Add a `Stringable` synthetic primitive (like `Number` is for `Int | Float`) representing "can be coerced to string via Nix interpolation". Use it as the upper bound constraint for interpolated sub-expressions.

Subtypes: `String <: Stringable`, `Path <: Stringable`, `AttrSet <: Stringable`.

## Changes

### `crates/lang_ty/src/primitive.rs`
- Add `Stringable` variant to enum
- Update `is_subtype_of()`: add `(String, Stringable) | (Path, Stringable)` arms

### `crates/lang_ty/src/arc_ty.rs`
- Add `PrimitiveTy::Stringable => write!(f, "stringable")` in Display impl

### `crates/lang_ty/src/disjoint.rs`
- Add early match arms BEFORE the cross-constructor catch-all:
  ```rust
  (Primitive(Stringable), AttrSet { .. }) | (AttrSet { .. }, Primitive(Stringable)) => false
  ```

### `crates/lang_check/src/constrain.rs`
- Add match arm in `constrain_concrete()` before the catch-all TypeMismatch:
  ```rust
  (Ty::AttrSet(_), Ty::Primitive(PrimitiveTy::Stringable)) => Ok(()),
  ```
- `String <: Stringable` and `Path <: Stringable` handled by existing `is_subtype_of()` arm.

### `crates/lang_check/src/infer_expr.rs`
- In the `StringInterpolation | PathInterpolation` handler (~line 496), after `self.infer_expr(*expr_id)?`, add:
  ```rust
  let expr_ty = self.ty_for_expr(*expr_id);
  let stringable = self.alloc_prim(PrimitiveTy::Stringable);
  self.constrain(expr_ty, stringable)?;
  ```

### `crates/lang_check/src/infer.rs`
- Add `Ty::Primitive(PrimitiveTy::Stringable)` to the `true` arm in `is_type_interpolable()`

### `crates/lang_check/src/pbt/mod.rs`
- Add `PrimitiveTy::Stringable` alongside `Number` in the `unreachable!` arm and the match at ~line 305

### `crates/lang_check/src/lib.rs`
- Add `"Stringable" => Some(PrimitiveTy::Stringable)` in primitive name lookup

### `crates/lang_check/src/builtins.rs`
- Add `(@ty $ctx:expr; Stringable) => { $ctx.alloc_prim(PrimitiveTy::Stringable) };`

### Files NOT modified
- `collect.rs` -- primitives canonicalize with trivial 1:1 projection
- `crates/lsp/` -- Display impl handles rendering automatically
- `crates/comment_parser/` -- not adding as parseable keyword yet (can be added later)

## Tests

- Interpolation constrains to stringable: `{ name ? null }: if name != null then "hello ${name}" else "No name"` infers `{ name?: stringable | null } -> string`
- `"${42}"` still errors (int is not stringable)
- `"${./foo}"` still works (path <: stringable)
- `foo` from `test/null.nix` still infers `{ name?: string | null } -> int` (string is more specific than stringable when `stringLength` also constrains)
