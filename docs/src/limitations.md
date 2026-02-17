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

No flow-sensitive typing. An `if x == "foo"` check doesn't narrow the type of `x` in the then-branch.

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
