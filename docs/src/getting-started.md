# Getting Started

## Install

### Try without installing

The fastest way to try tix — no installation required:

```bash
nix run github:JRMurr/tix -- my-file.nix

# With pre-generated NixOS + Home Manager type stubs:
nix run github:JRMurr/tix#with-stubs -- my-file.nix
```

### Nix Flake (recommended)

Add tix to your flake inputs:

```nix
{
  inputs.tix.url = "github:JRMurr/tix";
}
```

Then add the package to your system configuration:

```nix
# configuration.nix (NixOS)
{ inputs, pkgs, ... }:
{
  environment.systemPackages = [
    inputs.tix.packages.${pkgs.system}.default
    # Or for the variant with pre-generated stubs:
    # inputs.tix.packages.${pkgs.system}.with-stubs
  ];
}
```

Or add it to a dev shell:

```nix
{
  inputs.tix.url = "github:JRMurr/tix";

  outputs = { self, nixpkgs, tix, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        buildInputs = [
          tix.packages.x86_64-linux.with-stubs
        ];
      };
    };
}
```

Or install imperatively with `nix profile`:

```bash
nix profile install github:JRMurr/tix
```

### Without flakes

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

### Build from source

```bash
git clone https://github.com/JRMurr/tix
cd tix
cargo build --release
# Binaries at target/release/tix-cli and target/release/tix-lsp
```

Or with nix:

```bash
nix build .#
```

## Usage

### Type-check a file

```bash
tix-cli my-file.nix
```

This prints the inferred type of each top-level binding and the root expression.

### With stubs

```bash
tix-cli my-file.nix --stubs ./my-stubs/
```

`--stubs` accepts file paths or directories (recursively finds `.tix` files). Can be passed multiple times. The built-in nixpkgs stubs are loaded by default — use `--no-default-stubs` to disable.

### Generate stubs

Generate typed stubs from your NixOS or Home Manager configuration:

```bash
# From a flake
tix-cli gen-stubs nixos --flake . --hostname myhost -o nixos.tix
tix-cli gen-stubs home-manager --flake . --username jr -o hm.tix

# From nixpkgs directly
tix-cli gen-stubs nixos --nixpkgs /path/to/nixpkgs -o nixos.tix
```

See the [Stubs](./stubs.md) chapter for details.

### LSP

```bash
tix-lsp
```

Communicates over stdin/stdout. Works with any LSP-compatible editor. Supports the same `--stubs` and `--no-default-stubs` flags.

Features: hover types, completions (dot access, function args, identifiers), go-to-definition, find references, rename, inlay hints, document symbols, semantic tokens, formatting (via `nixfmt`).
