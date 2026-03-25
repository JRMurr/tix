# Cross-File Types

Tix supports type-level operators and cross-file type sharing, reducing the need for external `.tix` stub files for your own code.

## `typeof` — Reference Inferred Types

Use `typeof varname` in type annotations to reference the inferred type of a binding:

```nix
let
  scope = { mkDerivation = ...; lib = ...; };
  /** type: narrowed :: typeof scope */
  narrowed = scope;
in narrowed
```

The referenced binding must be in an earlier SCC group (already inferred). Mutually recursive bindings cannot use `typeof` on each other.

## Type Operators

### `Param(T)` and `Return(T)`

Extract the parameter or return type from a function type:

```nix
# Given: type F = int -> string -> bool;
# Param(F)         → int
# Return(F)        → string -> bool
# Param(Return(F)) → string
```

These work on type aliases, `typeof` results, and any type expression that resolves to a function:

```nix
let
  f = a: a + 1;
  /** type: x :: Param(typeof f) */
  x = 42;  # constrained to int (f's parameter type)
in x
```

### Field Access (`T.key`)

Extract the type of a field from an attrset type:

```nix
# Given: type Config = { name: string, age: int };
# Config.name → string
# Config.age  → int
```

Chained access works: `Config.meta.name` extracts nested fields.

## Cross-File Type Imports

### `import("./path.nix").TypeName`

Import a type declaration from another file's doc comments:

```nix
# lib.nix
/** type Input = { name: string, src: path, ... }; */
/** type Output = { name: string, system: string }; */
{ name, src, ... }: { inherit name; system = "x86_64-linux"; }
```

```nix
# consumer.nix
/** type: args :: import("./lib.nix").Input */
args: args.name
```

If the type declaration is a simple type (e.g. `{ name: string }`), this only reads the target file's doc comments — no inference required.

If the type declaration uses `typeof` (e.g. `type Scope = typeof scope;`), Tix runs **partial inference** on the target file — only the SCC groups needed to infer the referenced binding. This breaks potential cycles: even if file A imports file B at runtime, file B can still import A's type exports as long as the `typeof` target doesn't depend on B.

### `typeof import("./path.nix")`

Reference the inferred root type of another file:

```nix
# a.nix
{ x = 1; y = "hello"; }
```

```nix
# b.nix
/** type: data :: typeof import("./a.nix") */
data: data.x + 1
```

This **does** require inference of the target file. The same cycle detection as regular `import` applies — if A typeof-imports B and B imports A, it's an error.

## Composition

All operators compose:

```nix
# Extract the parameter type of a function from another file
/** type: buildInput :: Param(typeof import("./build.nix")) */

# Access a field on an imported type
/** type: lib :: import("./scope.nix").Scope.lib */

# Chain operators
/** type: x :: Return(Return(typeof f)) */
```

## When to Use Stubs vs Cross-File Types

| Scenario | Recommendation |
|----------|---------------|
| External deps (nixpkgs, etc.) | `.tix` stub files |
| Your own project's shared types | Doc comment type declarations + `import("path").TypeName` |
| Referencing inferred types within a file | `typeof varname` |
| Extracting parts of complex types | `Param(T)`, `Return(T)`, `T.key` |
