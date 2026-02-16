# Getting Started

## Install

### Nix Flake (recommended)

```bash
# Run directly
nix run github:JRMurr/tix -- my-file.nix

# With pre-generated NixOS + Home Manager stubs
nix run github:JRMurr/tix#with-stubs -- my-file.nix
```

To add tix to your project's dev shell:

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
