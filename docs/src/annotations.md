# Type Annotations

**TLDR:** Annotate bindings with doc comments when inference isn't enough. Two flavors: nixdoc-style `# Type` sections and inline `/** type: name :: Type */` comments.

## When you need annotations

Most code doesn't need annotations — tix infers types from usage. Annotations help when:

- You're importing external code that tix can't see into (e.g. `import ./lib.nix`)
- You want to constrain a binding to a specific type
- You want to document your API

## Doc comment format

### Nixdoc-style (multiline)

Follows the [nixdoc](https://github.com/nix-community/nixdoc) convention. The type goes in a fenced code block under a `# Type` heading:

````nix
/**
  Concatenate a list of strings with a separator.

  # Type

  ```
  concatStringsSep :: string -> [string] -> string
  ```
*/
concatStringsSep = sep: list: builtins.concatStringsSep sep list;
````

### Inline type annotation

For quick one-liners:

```nix
/** type: lib :: Lib */
lib = import ./lib.nix;

/** type: add :: int -> int -> int */
add = a: b: a + b;
# Without the annotation, `+` is overloaded and tix infers: a -> b -> c
# The annotation constrains it to integer addition only.
```

The `type:` prefix distinguishes it from regular doc comments.

### Assigning type aliases

When you import something typed by stubs, you assign it a type alias:

```nix
/** type: lib :: Lib */
lib = import ./lib.nix;

/** type: pkgs :: Pkgs */
pkgs = import <nixpkgs> {};
```

`Lib` and `Pkgs` are type aliases defined in the built-in stubs (or your custom `.tix` files). This tells tix "trust me, this import produces a value of this type."

## Type expression syntax

The same syntax works in doc comments and `.tix` stub files.

| Syntax | Meaning |
|--------|---------|
| `int`, `string`, `bool`, `float`, `path`, `null` | Primitives |
| `a`, `b` (lowercase) | Generic type variables |
| `Foo` (uppercase) | Type alias reference |
| `[a]` | List of `a` |
| `a -> b` | Function (right-associative) |
| `a \| b` | Union |
| `a & b` | Intersection |
| `{ name: string, age: int }` | Closed attrset |
| `{ name: string, ... }` | Open attrset |
| `{ _: int }` | Dynamic field type (all values are `int`) |

Precedence (low to high): `->` then `|` then `&` then atoms. Use parens to override.

```
(int | string) -> bool        # function from union to bool
(int -> int) & (string -> string)  # intersection of two function types
```
