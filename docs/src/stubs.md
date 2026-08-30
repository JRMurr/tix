# Stubs

**TLDR:** `.tix` files declare types for external Nix code — like TypeScript's `.d.ts` files. Tix ships with built-in stubs for common nixpkgs functions, and you can generate stubs from NixOS/Home Manager option trees.

## What are stubs?

Nix's `import` system makes full-program inference impractical. You're not going to infer all of nixpkgs. Stubs let you declare types for code that lives outside your project.

```bash
tix inspect my-file.nix --stubs ./my-stubs/
```

`--stubs` takes a file or directory (recursively finds `.tix` files). Can be passed multiple times. Built-in stubs load by default (`--no-default-stubs` to disable).

## Writing stubs

### Basic syntax

```tix
# Line comments

# Type aliases — lowercase vars are implicitly generic
type Derivation = { name: string, system: string, ... };
type Nullable = a | null;
# Aliases may be recursive under a list/function/attrset constructor
type Tree = { value: a, children: [Tree] };

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

### Custom context stubs from a file

For module systems not shipped as a built-in (e.g. flake-parts, devenv, custom
NixOS-like systems), point a context at a local `.tix` file. The file can use
either top-level `val` declarations or a `module` block — each field becomes
a context arg:

```toml
[context.flake-parts]
includes = ["modules/**/*.nix"]
stubs = ["./flake-parts.tix"]
```

```tix
# flake-parts.tix
module flakeparts {
    val config :: { perSystem: a -> b, ... };
    val lib :: Lib;
}
```

Files matching `modules/**/*.nix` see `config` and `lib` as typed lambda
parameters. When a top-level `val` and a module field share a name, the
top-level `val` wins (more explicit). Tix logs a warning if a stub file
produces zero context args — usually a sign that the file contains only
`type` aliases with no `val` or `module` declarations.

## Generating stubs from NixOS/Home Manager

Tix can generate stubs from NixOS options, Home Manager options, and nixpkgs package sets. This gives you typed access to `config`, `lib`, `pkgs`, and other parameters in your Nix files.

### From a flake

```bash
# NixOS options
tix stubs generate nixos --flake . --hostname myhost -o nixos.tix

# Home Manager options
tix stubs generate home-manager --flake . --username jr -o hm.tix
```

### From nixpkgs directly

```bash
tix stubs generate nixos --nixpkgs /path/to/nixpkgs -o nixos.tix
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
tix stubs generate pkgs -o generated-pkgs.tix
```

This evaluates nixpkgs and classifies each attribute:

- Derivations become `val hello :: Derivation;`
- Non-derivation attrsets become `val xorg :: { ... };`
- Functions become `val callPackage :: a -> b;`

Sub-package-sets like `llvmPackages`, `python3Packages`, and `xorg` that have `recurseForDerivations = true` are recursed into and emitted as nested modules:

```tix
module pkgs {
  val hello :: Derivation;
  module python313Packages {
    val numpy :: Derivation;
    val pandas :: Derivation;
  }
  val python3Packages :: Python313Packages;
  val writeText :: a -> b;
}
```

**Alias detection:** Nixpkgs uses `dontRecurseIntoAttrs` on alias package sets (e.g. `python3Packages = dontRecurseIntoAttrs python313Packages`). When a non-recursed attrset has `recurseForDerivations` explicitly set to `false` and its `builtins.attrNames` matches a recursed sibling, tix emits a type alias reference (`val python3Packages :: Python313Packages;`) instead of an opaque `{ ... }`. This gives alias sets the same typed fields as their targets.

Use `--max-depth` to control recursion depth (default: 1). Higher values give more coverage but increase eval time — `python3Packages` alone has ~10k attributes. Use `--max-depth 0` for flat output (no recursion).

The output is a `module pkgs { ... }` block that merges with the hand-curated `module pkgs` in the built-in stubs, extending the `Pkgs` type alias with thousands of additional fields. Since `@callpackage` derives its context from `Pkgs`, the generated packages are picked up automatically.

```bash
# Generate from specific nixpkgs
tix stubs generate pkgs --nixpkgs /path/to/nixpkgs -o generated-pkgs.tix

# Recurse deeper into sub-package-sets
tix stubs generate pkgs --max-depth 2 -o generated-pkgs.tix

# Flat output (no sub-package-set recursion, like pre-v0.x behavior)
tix stubs generate pkgs --max-depth 0 -o generated-pkgs.tix

# From pre-computed JSON (for reproducibility or CI)
tix stubs generate pkgs --from-json classified.json -o generated-pkgs.tix
```

Load the generated file via `--stubs` or the `stubs` config key:

```toml
stubs = ["./generated-pkgs.tix"]

[context.callpackage]
includes = ["pkgs/**/*.nix"]
stubs = ["@callpackage"]
```

### Using generated stubs with tix.toml

Once generated, point your `tix.toml` at them. See [Configuration](./configuration.md).

## Custom module systems (flake-parts, devenv, nix-darwin, ...)

For any module system that ships its own `evalModules`-style API, you
can generate typed stubs the same way NixOS and HM do. The flow is
**iterate with the CLI first, promote to tix.toml once happy**.

### 1. Iterate manually with the CLI

`tix stubs generate module` wraps an arbitrary options expression in
the generic extractor and emits a `.tix`. This gives immediate
feedback with no LSP restart loop.

```bash
tix stubs generate module \
  --name flake-parts \
  --options-expr '(inputs.flake-parts.lib.evalFlakeModule { self = self; } { imports = [ ]; }).options' \
  --context-arg config \
  --context-arg lib \
  --context-arg pkgs \
  -o flake-parts.tix
```

Inspect the output, tweak the expression, re-run. The generated file
contains a `type FlakePartsConfig = { ... }` alias and one `val`
declaration per `--context-arg`. Types are assigned by **name**, not
position: `config` → `FlakePartsConfig` (the options tree), `lib` →
`Lib`, `pkgs` → `Pkgs`, any other name → `{ ... }`. Order doesn't
matter — reordering the args produces the same output.

Optional two-step debugging:

```bash
# Inspect the raw options tree first.
nix eval --json --impure --expr '...' > options.json
tix stubs generate module --from-json options.json --name flake-parts ... -o flake-parts.tix
```

### 2. Promote to tix.toml

Once the CLI command produces a good stub, copy the expression into
`[stubs.generate.systems.<name>]`. The LSP runs the same pipeline on
startup and writes `<name>.tix` into its cache, so `@<name>` just
works as a context stub.

```toml
[stubs.generate]
nixpkgs = { expr = "(builtins.getFlake (toString ./.)).inputs.nixpkgs" }

[stubs.generate.systems.flake-parts]
options_expr = '''
  (inputs.flake-parts.lib.evalFlakeModule
    { self = self; } { imports = [ ]; }).options
'''
context_args = ["config", "lib", "pkgs"]

[context.flake-parts]
includes = ["flake-modules/**/*.nix"]
stubs = ["@flake-parts"]
```

### 3. Typing extra module args precisely

Args beyond `config`/`lib`/`pkgs` (e.g. flake-parts `withSystem`,
`inputs`, `self`; devenv `inputs'`) are typed as `{ ... }` in the
generated stub. That's enough for the checker to recognise the name,
but calls against it aren't checked — `withSystem "x86_64-linux" foo`
just returns an opaque attrset.

To give specific args precise types, write a companion `.tix` and
layer it **after** the generated stub in the context's `stubs`
array. Later entries override earlier ones on name collisions:

```tix
# flake-parts-extras.tix
val withSystem :: string -> a -> a;
val inputs :: { self: { ... }, nixpkgs: { ... }, ... };
```

```toml
[stubs.generate.systems.flake-parts]
options_expr = "..."
context_args = ["config", "lib", "pkgs", "withSystem", "inputs"]

[context.flake-parts]
includes = ["flake-modules/**/*.nix"]
stubs = ["@flake-parts", "./flake-parts-extras.tix"]  # extras win
```

The generated stub still types `config`/`lib`/`pkgs`; the extras
file refines `withSystem` and `inputs` to precise types. Top-level
`val` decls from all files in `stubs` are unioned into the context,
so extras.tix can also add new arg names not declared in
`context_args` at all — handy for iterating without re-running
`tix stubs refresh`.

### 4. After edits

The LSP generates custom-system stubs once at startup. If you change
the `options_expr`, `context_args`, or any module referenced from
them, run `tix stubs refresh` and restart the LSP.

## Refreshing generated stubs

Runtime-generated stubs (from `[stubs.generate]` in `tix.toml`) are
cached in `~/.cache/tix/store-stubs/`. The cache keys on the inputs
that feed into `nix build` — primarily the nixpkgs + home-manager
store paths — so bumping pinned inputs via `flake.lock` invalidates
the cache naturally.

The cache does **not** content-hash your own files. When you edit
anything that the stub pipeline depends on (e.g. a Nix expression in
`[stubs.generate]`, future user-module configurations), the cache
keeps serving stale stubs until you invalidate it manually:

```bash
tix stubs refresh
```

This clears the cache directory; the next run of the LSP or `tix
check` will re-invoke `nix build`. **Restart the LSP afterward** —
the LSP only runs stub generation at startup today.

## Source annotations

Stub declarations can carry `@source` annotations that link back to the
original source file. When present, **go-to-definition** in the LSP jumps
directly to the nixpkgs (or home-manager) source instead of landing in
the generated `.tix` file.

### Syntax

```
@source <source-id>:<relative-path>:<line>:<column>
```

For example:

```tix
@source nixpkgs:lib/trivial.nix:61:8
val id :: a -> a;
```

`@source` can appear before `val`, `type`, and `module` declarations, as
well as on individual attrset fields (used in NixOS/Home Manager option stubs).

### How it works

When stubs are generated with `--source-root nixpkgs=/nix/store/...-source`,
absolute Nix store paths from `builtins.unsafeGetAttrPos` are stripped against
the root to produce relative paths. At LSP startup the source root is resolved
(typically from the flake lock) so that go-to-definition can open the real file.

When using `[stubs.generate]` in `tix.toml`, source roots are passed
automatically — no manual `--source-root` flags needed.

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
