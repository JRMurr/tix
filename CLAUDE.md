# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Tix?

Tix is a type checker for the Nix language, implementing MLsub/SimpleSub — an extension of Hindley-Milner with subtyping, union types, and intersection types. Based on Parreaux's [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) (ICFP 2020).

## Build & Test Commands

```bash
cargo build                          # Build all crates
cargo test                           # Run all unit tests
cargo test --package lang_check      # Test a specific crate
cargo run --bin tix-cli test/basic.nix  # Type-check a Nix file
cargo fmt                            # Format (uses .rustfmt.toml)
cargo clippy                         # Lint
./pbt.sh                             # Property-based tests (50k cases default)
./pbt.sh 100000                      # PBT with custom case count
./cov.sh                             # Coverage report (cargo-tarpaulin)
```

Run a single test:
```bash
cargo test --package lang_check -- test_name
```

## Workspace Crates

Five crates under `crates/`, listed in pipeline order:

| Crate | Role |
|-------|------|
| `lang_ast` | Parse Nix via rnix, lower to Tix AST, name resolution, SCC grouping |
| `lang_ty` | Type representation: `Ty<R, VarType>` for inference, `OutputTy` with Union/Intersection for output |
| `comment_parser` | Parse type annotations from doc comments (pest grammar) |
| `lang_check` | SimpleSub type inference engine — the core of the project |
| `cli` | Thin binary entry point |

## Architecture & Pipeline

```
Nix source → [lang_ast::lower] Parse with rnix → Tix AST
           → [lang_ast::nameres] Name resolution + scope analysis
           → [lang_ast::group_def] SCC grouping for mutual recursion
           → [lang_check::check_file] Type inference (entry point)
               ├─ Pre-allocate TyIds for all names/expressions
               ├─ Per SCC group:
               │   ├─ [infer_expr] Single-pass AST walk, constrain() inline
               │   ├─ [constrain] Directional subtyping constraint recording
               │   ├─ Resolve deferred overloads/merges
               │   └─ [extrude] Level-based generalization
               └─ [collect::Collector] Canonicalize to OutputTy
           → CLI prints bindings and root type
```

### Key design decisions

- **Bounds-based variables, not union-find**: type variables store upper/lower bounds; `constrain(sub, sup)` propagates bounds inline (no separate solve phase).
- **Extrude replaces instantiate/generalize**: deep-level variables are copied to fresh variables at the current level with bounds linked via subtyping constraints.
- **Two type representations**: `Ty<R, VarType>` during inference (no union/intersection variants); `OutputTy` after canonicalization (has Union/Intersection).
- **Polarity-aware canonicalization**: positive positions expand to union of lower bounds; negative positions expand to intersection of upper bounds.
- **Salsa** for incremental computation (query caching).
- **Overload resolution is deferred**: operators like `+` and `*` are resolved after the SCC group is fully inferred.

### Key files for type inference

- `lang_check/src/infer.rs` — orchestration, SCC iteration, extrude, generalization
- `lang_check/src/infer_expr.rs` — single-pass AST inference walk
- `lang_check/src/constrain.rs` — core subtyping constraint function
- `lang_check/src/collect.rs` — canonicalization from bounds to OutputTy
- `lang_check/src/storage.rs` — bounds-based type variable storage
- `lang_check/src/builtins.rs` — Nix builtin type synthesis (uses `synth_ty!` macro)

## `.tix` Declaration Files (Stubs)

`.tix` files declare types for external Nix code (like TypeScript's `.d.ts`). They provide type information for things like nixpkgs lib functions that Tix can't infer on its own.

### Usage

```bash
cargo run --bin tix-cli -- test/stubs_test.nix --stubs stubs/
```

`--stubs` accepts file paths or directories (recursive `.tix` glob for dirs). Multiple `--stubs` flags can be passed.

### Syntax

```tix
# Line comments

# Type aliases (lowercase free vars are implicitly generic)
type Derivation = { name: string, system: string, ... };
type Nullable = a | null;

# Value declarations
val mkDerivation :: { name: string, src: path, ... } -> Derivation;

# Module nesting (auto-generates type alias from capitalized name)
module lib {
  val id :: a -> a;
  module strings {
    val concatStringsSep :: string -> [string] -> string;
  }
}
# ^ creates type alias "Lib" = { id: a -> a, strings: { ... }, ... }
```

### Integration with Nix files

Type aliases from stubs are referenced in doc comment annotations:

```nix
let
    /** type: lib :: Lib */
    lib = import ./lib.nix;
in
    lib.id 42  # inferred as int
```

Top-level `val` declarations (e.g. `val mkDerivation`) provide types for unresolved names automatically — no annotation needed:

```nix
mkDerivation { name = "my-package"; src = ./.; }
# ^ inferred as Derivation (i.e. { name: string, system: string, ... })
```

### Key files

- `stubs/lib.tix` — shipped nixpkgs lib stubs
- `comment_parser/src/tix_decl.pest` — `.tix` file grammar
- `comment_parser/src/tix_parser.rs` / `tix_collect.rs` — parser and collection
- `lang_check/src/aliases.rs` — `TypeAliasRegistry` (loads stubs, resolves aliases)

### Type expression syntax (shared by doc comments and `.tix` files)

| Syntax | Meaning |
|--------|---------|
| `int`, `string`, `bool`, `float`, `path`, `null` | Primitives |
| `a`, `b` (lowercase) | Implicit generic type variables |
| `Foo` (uppercase) | Reference to a type alias |
| `[a]` | List type |
| `a -> b` | Function type (right-associative) |
| `a \| b` | Union type |
| `a & b` | Intersection type |
| `{ name: string, age: int }` | Closed attrset |
| `{ name: string, ... }` | Open attrset |
| `{ _: int }` | Dynamic field type |

## Testing

- **Unit tests**: inline in each crate (`tests.rs`, `#[cfg(test)]` modules)
- **Property-based tests**: `lang_check/src/pbt/mod.rs` — generates arbitrary ASTs and types via proptest
- **Test fixtures**: Nix files in `test/` directory (e.g., `test/basic.nix`)

### LSP test conventions

LSP feature tests that need a cursor position should use **marker-based positioning** via `parse_markers()` from `test_util.rs`. Embed `# ^<num>` comments in the Nix source where `^` points to the column on the previous line:

```rust
let src = indoc! {"
    let x = 1; in x + x
    #   ^1         ^2
"};
let markers = parse_markers(src);
// markers[&1] = byte offset of the `x` definition
// markers[&2] = byte offset of the first `x` reference after `in`
```

Since `#` is a valid Nix comment, markers don't affect parsing. Prefer markers over `find_offset` + arithmetic (e.g. `find_offset(src, "in x") + 3`) — markers make the cursor position visually obvious and avoid fragile offset math. Plain `find_offset` is fine when it unambiguously lands on the right token (e.g. `find_offset(src, "1")` in `let x = 1`).

Use `indoc!` (from the `indoc` dev-dependency) for multiline test sources to avoid leading whitespace issues.
