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

## Generating stubs

Tix can generate stubs from NixOS and Home Manager option trees. This gives you typed access to `config`, `lib`, and `pkgs` parameters in module files.

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
