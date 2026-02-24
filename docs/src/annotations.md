# Type Annotations

**TLDR:** Annotate bindings with doc comments when inference isn't enough. Three flavors: nixdoc-style `# Type` sections, inline `/** type: name :: Type */` block comments, and `# type: name :: Type` line comments.

## When you need annotations

Most code doesn't need annotations — tix infers types from usage. Annotations help when:

- You're importing code via a path tix can't resolve (e.g. `import <nixpkgs>`, dynamic paths)
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

For quick one-liners, use either block comments or line comments:

```nix
/** type: lib :: Lib */
lib = import <nixpkgs/lib>;

/** type: add :: int -> int -> int */
add = a: b: a + b;
```

Line comments work too — handy for attrset pattern parameters where `/**` feels heavy:

```nix
{
  # type: pkgs :: Pkgs
  pkgs,
  # type: lib :: Lib
  lib,
}: ...
```

The `type:` prefix distinguishes annotations from regular comments.

### Assigning type aliases

When you import something typed by stubs, you assign it a type alias:

```nix
/** type: lib :: Lib */
lib = import <nixpkgs/lib>;

/** type: pkgs :: Pkgs */
pkgs = import <nixpkgs> {};
```

`Lib` and `Pkgs` are type aliases defined in the built-in stubs (or your custom `.tix` files). This tells tix "trust me, this import produces a value of this type."

## Type expression syntax

The same syntax works in doc comments and `.tix` stub files.

| Syntax | Meaning |
|--------|---------|
| `int`, `string`, `bool`, `float`, `path`, `null` | Primitives |
| `Int`, `String`, `Bool`, `Float`, `Path`, `Null` | Uppercase aliases (same as lowercase) |
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

### Uppercase primitives

Nixpkgs doc comments conventionally use uppercase names like `String`, `Bool`, and `Int`. Tix recognizes these as aliases for the lowercase primitives, so both `string` and `String` work in annotations.

## Inline Type Aliases

You can define type aliases directly in a `.nix` file using doc comments, without needing a separate `.tix` stub file:

```nix
/** type Derivation = { name: string, src: path, ... }; */
# type Nullable = a | null;

let
  /** type: mkDrv :: { name: string, ... } -> Derivation */
  mkDrv = { name, src, ... }: { inherit name; system = "x86_64-linux"; };
in ...
```

Both block (`/** ... */`) and line (`# type Foo = ...;`) comments work. The syntax is exactly the same as in `.tix` stub files — `type Name = TypeExpr;`.

Inline aliases are file-scoped (visible everywhere in the file regardless of placement) and shadow any aliases with the same name from loaded stubs.

**Disambiguation:** `type:` (with a colon) triggers a binding annotation (`type: name :: Type`). `type ` (with a space followed by an uppercase letter) triggers an alias declaration (`type Name = ...;`).

## Annotation safety

Tix applies annotations as bidirectional constraints — the inferred type must be compatible with the annotation and vice versa. Two situations cause annotations to be skipped with a warning instead of producing false errors:

**Arity mismatch.** If the annotation has fewer arrows than the function's visible lambda parameters (e.g. `foo :: string -> string` on a two-argument function `x: y: ...`), the annotation is skipped. An annotation with *more* arrows than visible lambdas is fine — the body may return a function (eta-reduction).

**Union types.** Annotations containing union types (e.g. `f :: string -> (string | [string]) -> string`) are currently skipped. Verifying union-typed parameters requires type narrowing for guards like `builtins.isList`, which is not yet fully implemented. The function is still type-checked based on its body alone.

**Intersection types (overloaded functions).** Annotations with intersection function types (e.g. `(int -> int) & (string -> string)`) are accepted as declared types for callers. The function body is type-checked based on inference alone — each component of the intersection is not individually verified against the body. This is useful for declaring overloaded APIs where the implementation uses type guards (`builtins.isInt`, etc.) to dispatch. An `AnnotationUnchecked` warning is emitted to indicate the annotation is trusted rather than verified.

## Named alias display in functions

When a function annotation references type aliases for its parameters, tix propagates the alias names through the function's lambda structure. This means the alias name is displayed instead of the expanded structural type:

```nix
# In a .tix stub:
# type BwrapArg = { escaped: string, ... } | string;

/** type: renderArg :: BwrapArg -> string */
renderArg = arg: ...;
```

Hovering over `renderArg` displays `BwrapArg -> string` rather than the fully expanded union/intersection type. This works for curried functions too — each parameter position preserves its alias name independently.
