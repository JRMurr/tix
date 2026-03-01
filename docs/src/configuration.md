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
- **stubs** — which stub sets to load. `@nixos` and `@home-manager` are built-in references to the generated NixOS/Home Manager stubs (requires the `with-stubs` package or `TIX_BUILTIN_STUBS` env var)

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

### Inference deadline

By default the LSP aborts type inference after 10 seconds per file and returns partial results. If you work with large files that need more time:

```toml
deadline = 30          # seconds per top-level file (default: 10)
```

### Generating tix.toml

Run `tix init` to automatically generate a `tix.toml` for your project:

```bash
tix-cli init              # Generate tix.toml in current project
tix-cli init --dry-run    # Preview without writing
tix-cli init --yes        # Overwrite existing tix.toml
tix-cli init /path/to/project  # Specify project directory
```

The command scans all `.nix` files, classifies each by its structural signals (parameter names, body references, attrset keys), and generates context sections mapping file paths to the appropriate stubs.

### No-module escape hatch

If tix incorrectly treats a file as a module, add this comment to disable module-aware features:

```nix
/** no-module */
```
