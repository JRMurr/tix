# Stubs

**TLDR:** `.tix` files declare types for external Nix code — like TypeScript's `.d.ts` files. Tix ships with built-in stubs for common nixpkgs functions, and you can generate stubs from NixOS/Home Manager option trees.

## What are stubs?

Nix's `import` system makes full-program inference impractical. You're not going to infer all of nixpkgs. Stubs let you declare types for code that lives outside your project.

```bash
tix-cli my-file.nix --stubs ./my-stubs/
```

`--stubs` takes a file or directory (recursively finds `.tix` files). Can be passed multiple times. Built-in stubs load by default (`--no-default-stubs` to disable).

## Writing stubs

### Basic syntax

```tix
# Line comments

# Type aliases — lowercase vars are implicitly generic
type Derivation = { name: string, system: string, ... };
type Nullable = a | null;

# Value declarations
val mkDerivation :: { name: string, src: path, ... } -> Derivation;

# Modules — nest values and create type aliases from the module name
module lib {
  val id :: a -> a;
  module strings {
    val concatStringsSep :: string -> [string] -> string;
  }
}
# ^ creates type alias "Lib" = { id: a -> a, strings: { concatStringsSep: ... }, ... }
```

### Type expressions

Same syntax as doc comment annotations — see [Type Annotations](./annotations.md#type-expression-syntax).

### Modules create type aliases

When you write `module foo { ... }`, tix auto-generates a type alias `Foo` (capitalized) representing the attrset type of that module's contents. This is how `Lib` and `Pkgs` work in the built-in stubs.

### Top-level `val` declarations

Top-level `val` declarations (outside any module) provide types for unresolved names automatically — no annotation needed in your Nix code:

```tix
val mkDerivation :: { name: string, ... } -> Derivation;
```

```nix
# No annotation needed — mkDerivation is resolved from stubs
mkDerivation { name = "my-pkg"; src = ./.; }
```

## Built-in stubs

Tix ships with stubs for common nixpkgs functions. These are compiled into the binary and loaded by default. They cover:

- **Pkgs**: `mkDerivation`, `stdenv.mkDerivation`, `fetchurl`, `fetchFromGitHub`, `runCommand`, `writeText`, etc.
- **Lib**: ~500 declarations covering `strings`, `lists`, `attrsets`, `trivial`, `fixedPoints`, `options`, `modules`, `fileset`, `filesystem`, `path`, `sources`, `versions`, `debug`, `generators`, `customisation`, `meta`, `asserts`, `gvariant`, `network`, and more. Generated from [noogle.dev](https://noogle.dev) data.
- **Derivation**: type alias for `{ name: string, system: string, builder: path | string, ... }`

Use `--no-default-stubs` if you want to replace them entirely with your own.

## Built-in context stubs

When used in a `tix.toml` context, `@`-prefixed stub names refer to built-in context sources:

| Stub | Source | Provides |
|------|--------|----------|
| `@nixos` | Compiled-in NixOS context stubs | `config`, `lib`, `pkgs`, `options`, `modulesPath` |
| `@home-manager` | Compiled-in Home Manager context stubs | `config`, `lib`, `pkgs`, `osConfig` |
| `@callpackage` | Derived from `Pkgs` module alias | All fields from `module pkgs` in the built-in stubs (`stdenv`, `fetchurl`, `lib`, `mkDerivation`, etc.) |

`@callpackage` doesn't require a separate stub file. It extracts the fields of the `Pkgs` type alias (created by `module pkgs { ... }` in the built-in stubs) and provides them as context args. This is the same mechanism that any `module foo { ... }` declaration uses: `@foo` resolves to `Foo`.

## Generating stubs

Tix can generate stubs from NixOS options, Home Manager options, and nixpkgs package sets. This gives you typed access to `config`, `lib`, `pkgs`, and other parameters in your Nix files.

### From a flake

```bash
# NixOS options
tix-cli gen-stubs nixos --flake . --hostname myhost -o nixos.tix

# Home Manager options
tix-cli gen-stubs home-manager --flake . --username jr -o hm.tix
```

### From nixpkgs directly

```bash
tix-cli gen-stubs nixos --nixpkgs /path/to/nixpkgs -o nixos.tix
```

### Options

| Flag | Description |
|------|-------------|
| `--flake PATH` | Flake directory to evaluate |
| `--hostname NAME` | NixOS hostname (required if multiple configurations) |
| `--username NAME` | Home Manager username (required if multiple configurations) |
| `--nixpkgs PATH` | Path to nixpkgs (default: `<nixpkgs>` from NIX_PATH) |
| `--from-json PATH` | Read pre-computed option tree JSON instead of running nix eval |
| `-o, --output PATH` | Output file (default: stdout) |
| `--max-depth N` | Maximum recursion depth for option tree walking (default: 8) |
| `--descriptions` | Include option descriptions as doc comments |

### Generating pkgs stubs

For `callPackage`-style files, you can auto-generate `val` declarations for all of nixpkgs:

```bash
tix-cli gen-stubs pkgs -o generated-pkgs.tix
```

This evaluates nixpkgs and classifies each attribute:

- Derivations become `val hello :: Derivation;`
- Non-derivation attrsets become `val xorg :: { ... };`
- Functions become `val callPackage :: a -> b;`

Sub-package-sets like `llvmPackages`, `python3Packages`, and `xorg` that have `recurseForDerivations = true` are recursed into and emitted as nested modules:

```tix
module pkgs {
  val hello :: Derivation;
  module llvmPackages {
    val clang :: Derivation;
    val llvm :: Derivation;
  }
  val writeText :: a -> b;
}
```

Use `--max-depth` to control recursion depth (default: 1). Higher values give more coverage but increase eval time — `python3Packages` alone has ~10k attributes. Use `--max-depth 0` for flat output (no recursion).

The output is a `module pkgs { ... }` block that merges with the hand-curated `module pkgs` in the built-in stubs, extending the `Pkgs` type alias with thousands of additional fields. Since `@callpackage` derives its context from `Pkgs`, the generated packages are picked up automatically.

```bash
# Generate from specific nixpkgs
tix-cli gen-stubs pkgs --nixpkgs /path/to/nixpkgs -o generated-pkgs.tix

# Recurse deeper into sub-package-sets
tix-cli gen-stubs pkgs --max-depth 2 -o generated-pkgs.tix

# Flat output (no sub-package-set recursion, like pre-v0.x behavior)
tix-cli gen-stubs pkgs --max-depth 0 -o generated-pkgs.tix

# From pre-computed JSON (for reproducibility or CI)
tix-cli gen-stubs pkgs --from-json classified.json -o generated-pkgs.tix
```

Load the generated file via `--stubs` or the `stubs` config key:

```toml
stubs = ["./generated-pkgs.tix"]

[context.callpackage]
paths = ["pkgs/**/*.nix"]
stubs = ["@callpackage"]
```

### Using generated stubs with tix.toml

Once generated, point your `tix.toml` at them. See [Configuration](./configuration.md).

## Using stubs in your code

Assign stub types to imports via doc comments:

```nix
let
  /** type: lib :: Lib */
  lib = import <nixpkgs/lib>;

  /** type: pkgs :: Pkgs */
  pkgs = import <nixpkgs> {};

  greeting = lib.strings.concatStringsSep ", " ["hello" "world"];
  drv = pkgs.stdenv.mkDerivation { name = "my-package"; src = ./.; };
in
{ inherit greeting drv; }
```

Now `lib.strings.concatStringsSep` is typed as `string -> [string] -> string`, and `drv` is typed as `Derivation`.
