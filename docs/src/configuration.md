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

`@callpackage` derives its types from the built-in `Pkgs` module (the same one that types `pkgs.stdenv.mkDerivation`, `pkgs.fetchurl`, etc.). Parameters not covered by the built-in stubs remain untyped. Extend with auto-generated stubs for broader coverage:

```toml
[context.callpackage]
paths = ["pkgs/**/*.nix"]
stubs = ["@callpackage", "./generated-pkgs.tix"]
```

See [Stubs: Generating pkgs stubs](./stubs.md#generating-pkgs-stubs) for how to generate `generated-pkgs.tix`.

### Inline context annotation

You can also set context per-file with a doc comment at the top:

```nix
/** context: nixos */
{ config, lib, pkgs, ... }:
{
  # ...
}
```

### Inference deadline

By default the LSP aborts type inference after 10 seconds per file (5 seconds per imported file) and returns partial results. If you work with large files that need more time, increase the deadlines:

```toml
deadline = 30          # seconds per top-level file (default: 10)
import_deadline = 15   # seconds per imported file (default: 5)
```

### No-module escape hatch

If tix incorrectly treats a file as a module, add this comment to disable module-aware features:

```nix
/** no-module */
```
