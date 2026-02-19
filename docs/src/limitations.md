# Limitations

Things tix doesn't support yet, or handles imperfectly.

## Language features

### `with` blocks

Only the innermost `with` environment is constrained for unresolved names. Nested `with` blocks don't fully fall through:

```nix
with a; with b;
  # names resolve against b, then a — but tix only constrains against b
  x
```

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

**Not yet supported:**
- Structural type predicates: `isAttrs`, `isFunction`, `isList` (these map to type constructors, not primitives — more complex to narrow)
- Multi-element attrpaths in `?`: `x ? a.b.c` doesn't narrow
- Compound conditions: `&&`, `||`
- Value equality narrowing: `if x == "foo"` doesn't narrow `x` to the literal `"foo"` (tix has no literal types)

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
