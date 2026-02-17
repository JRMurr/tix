# Internals

Implementation details for people who want to hack on tix or understand what's under the hood.

## Crates

Five crates under `crates/`, listed in pipeline order:

| Crate | Role |
|-------|------|
| `lang_ast` | Parse Nix via rnix, lower to Tix AST, name resolution, SCC grouping |
| `lang_ty` | Type representation: `Ty<R, VarType>` during inference, `OutputTy` for output |
| `comment_parser` | Parse type annotations from doc comments and `.tix` files (pest grammar) |
| `lang_check` | SimpleSub type inference engine |
| `lsp` | tower-lsp language server |
| `cli` | Binary entry points |

## Pipeline

```
Nix source
  → [lang_ast::lower] Parse with rnix → Tix AST
  → [lang_ast::nameres] Name resolution + scope analysis
  → [lang_ast::group_def] SCC grouping for mutual recursion
  → [lang_check::check_file] Type inference
      ├─ Pre-allocate TyIds for all names/expressions
      ├─ Per SCC group:
      │   ├─ [infer_expr] Single-pass AST walk, constrain() inline
      │   ├─ [constrain] Directional subtyping constraint recording
      │   ├─ Resolve deferred overloads/merges
      │   └─ [extrude] Level-based generalization
      └─ [collect::Collector] Canonicalize to OutputTy
  → CLI prints bindings and root type
```

## Key design decisions

### Bounds-based variables, not union-find

Type variables store upper/lower bounds. `constrain(sub, sup)` propagates bounds inline — there's no separate solve phase. This is the core difference from standard HM: instead of unifying variables, you record that one type must be a subtype of another.

### Extrude replaces instantiate/generalize

When a let-bound variable is referenced, its type is "extruded" — deep-level variables are copied to fresh variables at the current level with bounds linked via subtyping constraints. This replaces the traditional instantiate-then-generalize cycle.

### Two type representations

- `Ty<R, VarType>` during inference: 5 variants (TyVar, Primitive, List, Lambda, AttrSet). No union or intersection during inference.
- `OutputTy` after canonicalization: 7 variants (adds Union, Intersection).

This makes it impossible to accidentally construct a union type during inference. Union/intersection types only exist in the output.

### Polarity-aware canonicalization

When converting from internal bounds to output types:
- **Positive positions** (outputs, return types): variables expand to the union of their lower bounds
- **Negative positions** (inputs, parameters): variables expand to the intersection of their upper bounds
- Lambda params flip polarity

### Salsa for incremental computation

Type checking results are cached via [salsa](https://github.com/salsa-rs/salsa) queries. Re-checking after an edit only recomputes what changed.

### Overload resolution is deferred

Operators like `+` and `*` are overloaded across types. Resolution is deferred until the SCC group is fully inferred, then resolved based on concrete bounds. If bounds are still ambiguous, the overload is re-instantiated per call-site during extrusion.

## Key files

| File | Purpose |
|------|---------|
| `lang_check/src/infer.rs` | Orchestration, SCC iteration, extrude, generalization |
| `lang_check/src/infer_expr.rs` | Single-pass AST inference walk |
| `lang_check/src/constrain.rs` | Core subtyping constraint function |
| `lang_check/src/collect.rs` | Canonicalization from bounds to OutputTy |
| `lang_check/src/storage.rs` | Bounds-based type variable storage |
| `lang_check/src/builtins.rs` | Nix builtin type synthesis (`synth_ty!` macro) |
| `lang_ast/src/lower.rs` | Nix to Tix AST lowering |
| `lang_ast/src/nameres.rs` | Name resolution and scope analysis |
| `lang_ast/src/group_defs.rs` | SCC grouping for mutual recursion |
| `comment_parser/src/tix_decl.pest` | `.tix` file grammar |
| `comment_parser/src/tix_parser.rs` | `.tix` parser |
| `lang_check/src/aliases.rs` | Type alias registry (loads stubs, resolves aliases) |

## Testing

```bash
cargo test                        # All unit tests
cargo test --package lang_check   # Just the inference engine
./pbt.sh                          # Property-based tests (50k cases)
./pbt.sh 100000                   # PBT with custom count
./cov.sh                          # Coverage report (cargo-tarpaulin)
```

Property-based tests live in `lang_check/src/pbt/mod.rs` and generate arbitrary ASTs/types via proptest.

## Building

```bash
cargo build                       # Debug
cargo build --release             # Release
nix build .#                      # Nix
```

## References

- [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) (ICFP 2020) — the paper this is based on
- [MLstruct](https://dl.acm.org/doi/10.1145/3563304) (OOPSLA 2022) — potential future extension with negation types
- [The Simple Essence of Boolean-Algebraic Subtyping](https://doi.org/10.1145/3776689) (POPL 2026) — further extension with extensible records
- [nil](https://github.com/oxalica/nil) — Nix LSP, some code borrowed from here
- [hashing modulo alpha](https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf) — approach used for hashing types
