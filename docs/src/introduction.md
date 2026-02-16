# Introduction

Tix is a type checker for the [Nix](https://nixos.org/) language.

**TLDR:** It infers types for your Nix code using [MLsub/SimpleSub](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html), an extension of Hindley-Milner with subtyping. You get union types, intersection types, and row-polymorphic records without writing any annotations. When inference isn't enough (e.g. typing `lib` from nixpkgs), you annotate with doc comments or `.tix` stub files.

## Why

Nix is dynamically typed. This is fine for small configs but gets painful in larger codebases — you have to run code (or read it very carefully) to find type errors. Tix catches them statically.

The ideology: do as much inference as is reasonable but defer to doc comment annotations when it would be too hard to infer. Nix's `import` system, `with` blocks, and the sheer size of nixpkgs make full inference impractical. Instead, Tix infers what it can and lets you fill in the gaps with lightweight type annotations.

## What you get

- **Type inference** — most code needs zero annotations
- **Union types** — `if-then-else` with different branches, heterogeneous lists
- **Row polymorphism** — functions that access `x.foo` work on any attrset with a `foo` field
- **Operator overloading** — `+` on ints, floats, strings, and paths
- **Doc comment annotations** — when inference needs help
- **`.tix` stub files** — declare types for external code (nixpkgs lib, etc.)
- **Stub generation** — auto-generate stubs from NixOS/Home Manager option trees
- **LSP** — hover, completions, go-to-definition, rename, inlay hints, formatting
