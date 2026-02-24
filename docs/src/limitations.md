# Limitations

Things tix doesn't support yet, or handles imperfectly.

## Language features

### `with` blocks

Nested `with` blocks resolve names inner-to-outer, matching Nix runtime semantics:

```nix
with a; with b;
  # names resolve against b first, then a if b doesn't have the field
  x
```

The innermost `with` scope that contains the field wins, so shadowing works correctly. If no `with` scope has the field, a `MissingField` error is reported.

### Literal / singleton types

Tix doesn't have literal types. `"circle"` is typed as `string`, not as the literal `"circle"`. This means you can't do TypeScript-style discriminated unions:

```nix
# tix sees this as { type: string, radius: int } | { type: string, width: int }
# not { type: "circle", ... } | { type: "rect", ... }
```

### Type narrowing

Tix supports **type predicate narrowing** and **hasAttr narrowing**. Type predicate narrowing: when a condition checks `isNull x`, `isString x`, `isInt x`, `isFloat x`, `isBool x`, or `isPath x` (or `x == null`), the type of `x` is narrowed to the corresponding primitive in the then-branch. HasAttr narrowing: `x ? field` or `builtins.hasAttr "field" x` narrows `x` to have that field in the then-branch (single-key attrpaths only).

```nix
x: if x == null then "default" else x.name
# x is null in then-branch, non-null in else-branch — no error

x: if x ? name then x.name else "fallback"
# x is narrowed to have `name` in then-branch — no error
```

Narrowing also works with `assert`:

```nix
x: assert x != null; x.name
# x is non-null after the assert
```

Structural type predicates (`isAttrs`, `isFunction`, `isList`) have then-branch narrowing — `isAttrs x` narrows `x` to an attrset, `isList x` narrows to a list, and `isFunction x` narrows to a function. Else-branch narrowing for these compound types is not yet supported (no `¬{..}` / `¬[..]` / `¬(a → b)`).

Short-circuit narrowing is supported for `&&` and `||`:

```nix
x: x == null || x + 1 > 0
# RHS of || runs when x != null — x is narrowed to non-null

x: x != null && builtins.isString x.name
# RHS of && runs when x != null — x is narrowed to non-null
```

**Not yet supported:**
- Else-branch narrowing for structural predicates (`isAttrs`, `isList`, `isFunction`)
- Multi-element attrpaths in `?`: `x ? a.b.c` doesn't narrow
- Value equality narrowing: `if x == "foo"` doesn't narrow `x` to the literal `"foo"` (tix has no literal types)
- Per-component verification of intersection-of-function annotations (the declared overloaded type is trusted, not checked against each branch of the body)
- Recursive functions with type-narrowed parameters: `isFunction x` in one branch + recursive call from another branch share the same type variable, causing false positive conflicts

### `inherit (builtins)` and dynamic field access

Dynamic attrset field access (`x.${name}`) uses the dynamic field type `{_: a}` but can't track which specific field is being accessed.

## Type inference

### Deferred overloads across files

Overloaded operators (like `+` with free type variables) don't survive the `OutputTy` boundary between files. If a polymorphic function using `+` is imported from another file, the overload may not resolve correctly.

### Recursive attrsets

`rec { ... }` works but equirecursive types (types that refer to themselves) can produce verbose output in some cases.

## Stubs and generation

### nixpkgs lib

The built-in stubs cover common `lib` functions but not all of nixpkgs lib. Functions not covered get fresh type variables (no error, just no type info).

### Stub generation

- NixOS stub generation works well for option trees
- Home Manager flake mode is less tested
- lib function stubs are hand-written (no auto-generation from nixpkgs lib source yet)
- Enum option types become `string` (no literal type support)
