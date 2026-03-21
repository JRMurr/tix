# Configuration

**TLDR:** `tix.toml` maps file paths to contexts (like `@nixos` or `@home-manager`), controlling which stubs get loaded and how module parameters are typed.

## tix.toml

Tix auto-discovers `tix.toml` by walking up from the file being checked. You can also pass `--config path/to/tix.toml` explicitly.

### Contexts

A context tells tix "files matching these paths are NixOS modules (or Home Manager modules, etc.)" so it knows how to type the standard `{ config, lib, pkgs, ... }:` parameter pattern.

```toml
[context.nixos]
paths = ["modules/*.nix", "hosts/**/*.nix"]
stubs = ["@nixos"]

[context.home-manager]
paths = ["home/*.nix"]
stubs = ["@home-manager"]
```

- **paths** — glob patterns matching files in this context
- **exclude** — glob patterns for files to exclude even when `paths` matches. Useful when a broad glob like `dir/**/*.nix` covers a directory with a few files that belong to a different context.
- **stubs** — which stub sets to load. `@nixos` and `@home-manager` are built-in references to the generated NixOS/Home Manager stubs (requires [`[stubs.generate]`](#runtime-stub-generation) or the `TIX_BUILTIN_STUBS` env var)

For example, if most files under `common/` are NixOS modules but `common/homemanager/` contains Home Manager modules:

```toml
[context.nixos]
paths = ["common/**/*.nix", "hosts/**/*.nix"]
exclude = ["common/homemanager/**/*.nix"]
stubs = ["@nixos"]

[context.home-manager]
paths = ["common/homemanager/**/*.nix"]
stubs = ["@home-manager"]
```

`tix init` generates `exclude` patterns automatically when it detects mixed-kind directories.

### What contexts do

When a file matches a context, tix automatically types the module's function parameters. A NixOS module like:

```nix
{ config, lib, pkgs, ... }:
{
  services.foo.enable = true;
}
```

Gets `config`, `lib`, and `pkgs` typed according to the context's stubs, without any doc comment annotations in the file.

### callPackage / dependency-injected files

For files loaded via `callPackage` or `import` that take a package set as their parameter:

```toml
[context.callpackage]
paths = ["pkgs/**/*.nix"]
stubs = ["@callpackage"]
```

`@callpackage` derives its types from the built-in `Pkgs` module (the same one that types `pkgs.stdenv.mkDerivation`, `pkgs.fetchurl`, etc.). Parameters not covered by the built-in stubs remain untyped. For broader coverage, [generate pkgs stubs](./stubs.md#generating-pkgs-stubs) and load them via `--stubs` or the `stubs` config key — they merge into the `Pkgs` type alias automatically.

### Inline context annotation

You can also set context per-file with a doc comment at the top:

```nix
/** context: nixos */
{ config, lib, pkgs, ... }:
{
  # ...
}
```

### Project settings

The `[project]` section configures project-level behavior for both the LSP and `tix check`.

```toml
[project]
analyze = ["lib/*.nix", "pkgs/**/*.nix"]
exclude = ["result", ".direnv", "vendor/**"]
```

- **analyze** — glob patterns for files to analyze in the background when the LSP starts. Their inferred types become ephemeral stubs available to all open files.
- **exclude** — glob patterns for files/directories to skip during `tix check`. Hardcoded ignores (`.git`, `node_modules`, `result`, `.direnv`, `target`) are always applied.

`tix init` generates a `[project]` section with sensible defaults.

Files matching `analyze` are processed in the background after LSP initialization. As each file's type is inferred, any open files that import it are automatically re-analyzed with the updated type information.

### Diagnostics

Control the severity of optional diagnostics. Currently the only configurable diagnostic is `unknown_type` ([E014](./diagnostics/e014.md)), which fires when a binding has type `?`.

```toml
[diagnostics]
unknown_type = "hint"  # "off", "hint", "warning", or "error" (default: "hint")
```

The LSP editor settings (`tix.diagnostics.unknownType`) take precedence over `tix.toml` when both are set.

### Runtime stub generation

Tix can generate full NixOS, Home Manager, and pkgs stubs at runtime on first use. The result is cached in the Nix store and reused on subsequent runs.

```toml
[stubs.generate]
nixpkgs = "/nix/store/...-nixpkgs-src"
home-manager = "/nix/store/...-home-manager-src"
```

Each source can be a direct store path or a Nix expression:

```toml
[stubs.generate]
nixpkgs = { expr = "(builtins.getFlake (toString ./.)).inputs.nixpkgs" }
home-manager = { expr = "(builtins.getFlake (toString ./.)).inputs.home-manager" }
```

- **nixpkgs** (required) — path to nixpkgs source, or `{ expr = "..." }` to evaluate
- **home-manager** (optional) — path to home-manager source; omit to skip HM stubs

On first run, tix invokes `nix build` to generate `.tix` stubs from the NixOS option tree, Home Manager options, and nixpkgs package set. This takes 30-60 seconds. Subsequent runs are instant thanks to a lightweight file cache (`~/.cache/tix/store-stubs/`). Changing either nixpkgs or tix version triggers regeneration.

`[stubs.generate]` can coexist with manual stub paths:

```toml
[stubs]
paths = ["./my-extra-stubs/"]

[stubs.generate]
nixpkgs = { expr = "(builtins.getFlake (toString ./.)).inputs.nixpkgs" }
```

**Resolution priority:**
1. `TIX_BUILTIN_STUBS` env var (always wins)
2. `[stubs.generate]` runtime generation
3. Compiled-in minimal stubs

**Requirements:** The tix binary must be installed via Nix (running from `/nix/store/...`). In dev mode (cargo build), use `TIX_BUILTIN_STUBS` or `nix build .#stubs` instead.

### Generating tix.toml

Run `tix init` to automatically generate a `tix.toml` for your project:

```bash
tix init              # Generate tix.toml in current project
tix init --dry-run    # Preview without writing
tix init --yes        # Overwrite existing tix.toml
tix init /path/to/project  # Specify project directory
```

The command scans all `.nix` files, classifies each by its structural signals (parameter names, body references, attrset keys), and generates context sections mapping file paths to the appropriate stubs.

### No-module escape hatch

If tix incorrectly treats a file as a module, add this comment to disable module-aware features:

```nix
/** no-module */
```
