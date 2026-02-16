# Tix

A type checker for Nix, built on [MLsub/SimpleSub](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) — Hindley-Milner extended with subtyping, union types, and intersection types.

The ideology: do as much inference as is reasonable but defer to doc comment annotations when it would be too hard to infer.

## Quick Start

### Install via Nix Flake

```bash
# Run directly
nix run github:JRMurr/tix -- my-file.nix

# Or add to your flake inputs
{
  inputs.tix.url = "github:JRMurr/tix";
}
```

The `with-stubs` package includes pre-generated NixOS and Home Manager type stubs:

```bash
nix run github:JRMurr/tix#with-stubs -- my-file.nix
```

### Type-check a file

```bash
tix-cli my-file.nix
```

### Use the LSP

```bash
tix-lsp
```

Works with any editor that supports LSP. Provides hover types, completions, go-to-definition, rename, inlay hints, and more.

### CLI flags

```
tix-cli <file.nix> [--stubs path/to/stubs/] [--no-default-stubs] [--config tix.toml]
tix-cli gen-stubs nixos [--flake .] [--hostname myhost] [-o nixos.tix]
tix-cli gen-stubs home-manager [--flake .] [--username jr] [-o hm.tix]
```

## What does it do?

Given a Nix file like:

```nix
let
  add = a: b: a + b;
  result = add 1 2;
  greeting = if result > 0 then "positive" else null;
in
{ inherit add result greeting; }
```

Tix infers:

```
add     :: int -> int -> int
result  :: int
greeting :: string | null
```

Union types fall out naturally — `if-then-else` with different branch types, heterogeneous lists, etc. all just work.

## Documentation

Full docs (type system, stubs, configuration, internals): `docs/` directory, built with mdbook.

```bash
cd docs && mdbook serve
```

## Links

- [nil](https://github.com/oxalica/nil) — Nix LSP that does some type inference. Read over its source a lot and took some code from there to get started.
- [nix-types RFC](https://github.com/hsjobeki/nix-types/blob/main/docs/README.md#nix-types-rfc-draft) — good spec for parsing doc comments
- [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) — the paper this is based on
