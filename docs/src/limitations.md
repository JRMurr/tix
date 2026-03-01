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

If no `with` scope has the field, a `MissingField` error is reported.

### Literal / singleton types

Tix doesn't have literal types. `"circle"` is typed as `string`, not as the literal `"circle"`. This means you can't do TypeScript-style discriminated unions:

```nix
# tix sees this as { type: string, radius: int } | { type: string, width: int }
# not { type: "circle", ... } | { type: "rect", ... }
```

Enum option types in generated NixOS stubs also become `string` for this reason.

### Dynamic field access

Dynamic attrset field access (`x.${name}`) uses a general dynamic field type but can't track which specific field is being accessed.

## Type narrowing

Narrowing works well for most common patterns (see [Type System](./type-system.md#type-narrowing)), but has some gaps:

- **Structural predicates** (`isAttrs`, `isList`, `isFunction`) only narrow in the then-branch. The else-branch doesn't exclude these types.
- **Multi-element attrpaths**: `x ? a.b.c` doesn't narrow — only single-key `x ? field` works.
- **Value equality**: `if x == "foo"` doesn't narrow `x` to the literal `"foo"` (no literal types).
- **Overloaded function annotations**: intersection-type annotations (e.g. `(int -> int) & (string -> string)`) are trusted, not verified per-branch.
- **Recursive narrowing**: using `isFunction x` in one branch and recursing from another can cause false positives because both branches share the same type variable.

## Cross-file inference

- **Imports without stubs** are inferred as `any` (the top type). For precise cross-file types, use `[project] analyze` in `tix.toml` or generate stubs with `gen-stub`.
- **Overloaded operators** (like `+` with polymorphic arguments) don't survive file boundaries. If a generic function using `+` is imported from another file, the overload may not resolve correctly.

## Recursive attrsets

`rec { ... }` works but types that refer to themselves can produce verbose output in some cases.

## Stubs

- The built-in lib stubs cover common functions but not all of nixpkgs lib. Unstubbed functions get a fresh type variable (no error, just no type info).
- Home Manager flake mode stub generation is less tested than NixOS.
- lib function stubs are curated from [noogle.dev](https://noogle.dev) data — there's no auto-generation from nixpkgs lib source yet.
