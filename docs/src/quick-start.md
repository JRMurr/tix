# Quick Start

Get tix running on an existing Nix project in under five minutes.

## 1. Install

The fastest way — no install required:

```bash
nix run github:JRMurr/tix -- inspect my-file.nix
```

For permanent use, add to your flake's `devShell` or install with `nix profile`:

```bash
nix profile install github:JRMurr/tix
```

See [Getting Started](./getting-started.md#install) for all installation options.

## 2. Initialize your project

From your project root:

```bash
tix init
```

This scans your `.nix` files, classifies them (NixOS module, Home Manager module, callPackage, etc.), and writes a `tix.toml`. Preview first with `tix init --dry-run`.

## 3. Stub generation

For flake projects, `tix init` auto-detects your nixpkgs (and home-manager) inputs from `flake.lock` and adds a `[stubs.generate]` section. On first run, tix builds rich type stubs from your nixpkgs (~30-60s); subsequent runs are cached.

For non-flake projects, add the section manually:

```toml
[stubs.generate]
# any nix expression that resolves to a nixpkgs path
nixpkgs = { expr = "(<import pinned_nixpkgs>).path" }
```

See [Configuration > Runtime stub generation](./configuration.md#runtime-stub-generation) for details.

## 4. Check your project

```bash
tix check
```

This type-checks every `.nix` file in your project, applying the contexts from `tix.toml`. Files are processed in dependency order so types flow across imports.

Or use the LSP for inline feedback in your editor:

```bash
tix lsp
```

See [LSP](./lsp.md) for editor setup instructions.

## 5. Suppress false positives

Tix won't understand everything — some files may produce errors you want to silence for now.

Suppress all diagnostics for a file:

```nix
# tix-nocheck
{ config, lib, pkgs, ... }:
{
  # nothing in this file is checked
}
```

Suppress a single line:

```nix
let
  # tix-ignore
  x = somethingTixDoesntUnderstand;
in
  x
```

See [Configuration > Suppression directives](./configuration.md#suppression-directives) for more.
