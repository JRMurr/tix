# Internals

This section covers implementation details for contributors and anyone curious about how tix works under the hood. None of this is needed to use tix effectively.

## Type theory background

Tix implements [MLsub/SimpleSub](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) — an extension of Hindley-Milner with subtyping (ICFP 2020). It extends this with Boolean-Algebraic Subtyping (BAS) for negation types and type narrowing, following [Chau & Parreaux (POPL 2026)](https://github.com/fo5for/sebas).

### Key design decisions

- **Bounds-based variables, not union-find**: type variables store upper/lower bounds; `constrain(sub, sup)` propagates bounds inline (no separate solve phase).
- **Extrude replaces instantiate/generalize**: deep-level variables are copied to fresh variables at the current level with bounds linked via subtyping constraints. This is SimpleSub's key insight — it replaces the traditional Hindley-Milner generalize/instantiate pair with a single operation.
- **Two type representations**: `Ty<R, VarType>` during inference (includes `Neg`, `Inter`, `Union` for narrowing); `OutputTy` after canonicalization (has Union/Intersection/Neg).
- **Polarity-aware canonicalization**: positive positions expand to union of lower bounds; negative positions expand to intersection of upper bounds.
- **SCC grouping**: mutually recursive bindings are grouped into strongly connected components and inferred together. Each SCC is fully inferred before moving to the next.
- **Deferred overload resolution**: operators like `+` are resolved after the SCC group is fully inferred, when more type information is available.
- **Salsa** for incremental computation (query caching in the LSP).

## How narrowing works

Narrowing uses first-class intersection types during inference (following the [MLstruct approach from OOPSLA 2022](https://infoscience.epfl.ch/record/299030)). When `isString x` is the condition:

- **Then-branch**: x gets type `α ∧ string` (an intersection of the original type variable with string)
- **Else-branch**: x gets type `α ∧ ~string` (intersection with negation)

These intersection types are structural — they flow through constraints, extrusion, and generalization like any other type. This means narrowing information survives let-polymorphism:

```nix
let f = x: if isNull x then 0 else x; in f
# f :: a -> int | ~null
# The ~null constraint on the else-branch's x is preserved
```

When a narrowed type like `α ∧ ~null` flows into a function that expects `string`, the solver applies variable isolation (the "annoying" constraint decomposition from MLstruct): `α ∧ ~null <: string` becomes `α <: string | null`, correctly constraining α without losing the negation information.

### Negation normalization

Negation types are normalized during canonicalization using standard Boolean algebra rules:

- **Double negation**: `~~T` simplifies to `T`
- **De Morgan (union)**: `~(A | B)` becomes `~A & ~B`
- **De Morgan (intersection)**: `~(A & B)` becomes `~A | ~B`
- **Contradiction**: `T & ~T` or `string & int` in an intersection is detected as uninhabited and displayed as `never`
- **Tautology**: `T | ~T` in a union is detected as universal and simplifies to `any` (the top type)
- **Redundant negation**: `{name: string} & ~null` simplifies to `{name: string}` (attrsets are inherently non-null)
- **Union absorption**: `{...} | {x: int, ...}` simplifies to `{...}` — an open attrset with fewer required fields subsumes more specific open attrsets
- **Intersection factoring**: `(A | C) & (B | C)` simplifies to `C | (A & B)` — shared members across all union terms are factored out using the distributive law

## LSP architecture

### Event coalescing

Instead of per-file timer debouncing, the LSP uses an event-coalescing architecture inspired by rust-analyzer. `didChange` and `didOpen` notifications send events to a single analysis loop. The loop drains all pending events before starting analysis, naturally batching rapid edits without artificial delays. Diagnostic publication is deferred behind a 200ms quiescence timer to prevent flickering during rapid typing, but analysis results are available to interactive requests (hover, completion) immediately.

Completion works responsively during editing. When a completion request arrives before the latest analysis finishes, the server first tries full completion against the fresh parse tree. If that fails, it falls back to a syntax-only path that provides both dot completion (via name-text lookup against the stale analysis) and identifier completion (variable names from the scope chain).

### Cancellation

When a new edit arrives for a file that's currently being analyzed, the in-flight analysis is cancelled via a cooperative cancellation flag. The inference engine checks this flag between SCC groups and periodically during constraint propagation, so cancellation typically takes effect within milliseconds.

## Key source files

| File | Role |
|------|------|
| `lang_check/src/infer.rs` | Orchestration, SCC iteration, extrude, generalization |
| `lang_check/src/infer_expr.rs` | Single-pass AST inference walk |
| `lang_check/src/constrain.rs` | Core subtyping constraint function |
| `lang_check/src/collect.rs` | Canonicalization from bounds to OutputTy |
| `lang_check/src/storage.rs` | Bounds-based type variable storage |
| `lang_check/src/builtins.rs` | Nix builtin type synthesis |
| `lang_ast/src/narrow.rs` | Guard recognition, NarrowPredicate enum |
| `comment_parser/src/tix_decl.pest` | `.tix` file grammar |
| `lang_check/src/aliases.rs` | TypeAliasRegistry (loads stubs, resolves aliases) |

## References

- Parreaux, [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html) (ICFP 2020) — the core type system
- Parreaux & Chau, [MLstruct](https://infoscience.epfl.ch/record/299030) (OOPSLA 2022) — negation types and pattern matching
- Chau & Parreaux, [Simple Essence of Boolean-Algebraic Subtyping](https://github.com/fo5for/sebas) (POPL 2026) — BAS reference implementation
- See `docs/internal/narrowing-design.md` for full narrowing design rationale
