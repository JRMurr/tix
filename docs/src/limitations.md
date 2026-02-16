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

### Co-occurrence simplification

Not yet implemented. Some inferred types are more complex than necessary:

```nix
apply = fn: args: fn args;
# Inferred: (int | string) -> a  (instead of a -> b)
```

The SimpleSub paper's Section 4.2 describes co-occurrence analysis that would fix this.

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

## LSP

### Incomplete expressions

rnix's error recovery on incomplete code (e.g. typing `pkgs.` with nothing after the dot) can cascade and mangle subsequent expressions. The LSP does its best but completion/hover may be wrong in partially-written code.

### Multi-element attrpath hover

Hovering over `a.foo.bar` shows the result type of the full chain, not intermediate types. You can't hover over just `a.foo` to see its type mid-chain.

## Performance

Tix is fast for individual files. Checking large multi-file projects with lots of imports may be slow since each import is re-analyzed (salsa caching helps for repeated checks in LSP mode).
