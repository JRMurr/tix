# Tix

A type checker for Nix, built on [MLsub/SimpleSub](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) — Hindley-Milner extended with subtyping, union types, and intersection types.

The goal is to have inference do as much of the work as possible but when it gets really nasty allow manually specified types through doc comments.

TLDR: try to be typescript for nix

## Quick Start

### Installation

<details>
  <summary>nix run (try without installing)</summary>

```bash
nix run github:JRMurr/tix -- my-file.nix

# With pre-generated NixOS and Home Manager type stubs:
nix run github:JRMurr/tix#with-stubs -- my-file.nix
```

</details>

<details>
  <summary>Flake (NixOS / Home Manager / nix profile)</summary>

Add tix to your flake inputs:

```nix
{
  inputs.tix.url = "github:JRMurr/tix";
}
```

Then add the package to your config, e.g. in NixOS:

```nix
# configuration.nix
{ inputs, pkgs, ... }:
{
  environment.systemPackages = [
    inputs.tix.packages.${pkgs.system}.default
    # Or for the variant with pre-generated stubs:
    # inputs.tix.packages.${pkgs.system}.with-stubs
  ];
}
```

Or install imperatively with `nix profile`:

```bash
nix profile install github:JRMurr/tix
```

</details>

<details>
  <summary>Without flakes (traditional NixOS / nix-env)</summary>

Add to a traditional NixOS configuration via `fetchTarball`:

```nix
# configuration.nix
let
  tix = import (builtins.fetchTarball "https://github.com/JRMurr/tix/archive/main.tar.gz") {};
in
{
  environment.systemPackages = [
    tix.packages.${builtins.currentSystem}.default
    # Or for the variant with pre-generated stubs:
    # tix.packages.${builtins.currentSystem}.with-stubs
  ];
}
```

Pin to a specific revision for reproducibility:

```nix
let
  tix = import (builtins.fetchTarball {
    url = "https://github.com/JRMurr/tix/archive/<rev>.tar.gz";
    sha256 = "<hash>";  # nix-prefetch-url --unpack <url>
  }) {};
in
  tix.packages.${builtins.currentSystem}.default
```

Or install imperatively with `nix-env`:

```bash
nix-env -f https://github.com/JRMurr/tix/archive/main.tar.gz -iA packages.x86_64-linux.default
```

</details>

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
