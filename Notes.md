# MLstruct vs SimpleSub for Nix

MLstruct is Parreaux's follow-up to SimpleSub (same author). It extends the type system with **negation/complement types**, forming a full Boolean algebra of types (union ∨, intersection ∧, negation ¬). The key question is whether those additions help with tix's specific pain points.

## What MLstruct adds

### 1. Negation types enable "exact" records without row variables

The current attrset representation uses an `open: bool` flag to control width subtyping. This is a binary choice — either the record can have extra fields or it can't. MLstruct can express things like `{ foo: int } ∧ ¬{ bar: ⊤ }` — "has foo, definitely doesn't have bar." This is more expressive than the current open/closed distinction.

For Nix this matters because `//` (attrset merge) and pattern destructuring need to reason about which fields are present/absent. The current `pending_merges` approach defers this reasoning; MLstruct could handle it structurally.

A more recent paper (POPL 2026, "The Simple Essence of Boolean-Algebraic Subtyping") expands on this: BAS is already powerful enough to encode the removal of a field from a type, allowing support for extensible records through one new term form and one new typing rule, but, surprisingly, no changes to subtyping at all.

### 2. Extensible variants without row variables

SimpleSub produces unions naturally (`if-then-else` already does this), but MLstruct's Boolean algebra lets you express *subtraction* from unions — e.g., a function that handles one case of a tagged union and returns the remaining cases. This is the pattern matching / exhaustiveness story.

For Nix, this is less immediately useful since Nix doesn't have algebraic data types or pattern matching on tagged values. The closest analog is `if x.type == "foo" then ... else ...` type narrowing.

### 3. Better type simplification

This is probably the most directly relevant benefit. The current unsolved issue is that `apply = fn: args: fn args` shows use-site contamination (`(int | string) -> a` instead of `a -> b`). SimpleSub's Section 4.2 co-occurrence analysis can fix this, but MLstruct goes further with Boolean algebra simplification — disjunctive normal forms, complement simplification, factorizing common conjuncts. These are more principled than ad-hoc co-occurrence merging.

Key details on co-occurrence analysis (from Section 4.2 of the SimpleSub paper):
- Co-occurrence analysis cannot be performed on non-expanded types, since it will miss information contained in bounds that have not been flattened yet.
- The result of co-occurrence analysis can be used to remove variables which are sandwiched between two identical bounds.
- A type such as `bool -> a -> b -> a | b` (the natural type of if-then-else) is equivalent to the simpler `bool -> a -> a -> a`, because the positive occurrences of a and b are "indistinguishable."
- All these transformations are truly simplifications that yield new types with fewer subterms but still equivalent to the original types, and therefore they preserve principality.

### 4. Principal inference with first-class unions/intersections

SimpleSub keeps unions strictly positive and intersections strictly negative during inference. MLstruct relaxes this by using the Boolean algebra to normalize mixed-polarity types. This would help with the overloaded binop situation — instead of deferred overloads, you could give `+` the intersection type `(int -> int -> int) & (float -> float -> float) & (string -> string -> string)` and have it work correctly in both polarities.

## Where MLstruct is overkill or doesn't help

- **Nominal classes**: MLstruct uses class-based nominality for extensible variants. Nix has no classes or nominal types, so this feature is dead weight.
- **Complexity**: MLstruct's inference is significantly more complex than SimpleSub. The subtyping problem for the full Boolean algebra is co-NP-hard (though practical cases are fast). You'd be trading implementation complexity for type-system expressiveness.
- **Equirecursive types**: MLstruct supports these; useful for Nix's recursive attrsets (`rec { ... }`), but you could add equirecursive types to SimpleSub independently.

Note on negation types: the interpretation is considerably constrained. In practice, the intuition that the values of `~t` are those that are not of type `t` only holds when `t` is a nominal tag in MLstruct. For other constructs, such as functions and records, negations assume a purely algebraic role.

## Practical assessment for tix

| Problem | SimpleSub fix | MLstruct fix |
|---------|--------------|--------------|
| `apply` contamination | Co-occurrence analysis (Section 4.2) | Boolean algebra simplification (more principled) |
| Overloaded binops | Deferred overloads (current) or intersection types | First-class intersection types (native) |
| Attrset merge precision | `pending_merges` + open/closed flag | Negation types for field presence/absence |
| Missing field errors | Binary open/closed | Negation types (more precise) |
| Type narrowing | Not supported | Negation enables it structurally |

**Assessment**: The two features that would most help tix are (1) proper type simplification and (2) first-class intersection types for overloading. You can get (1) by implementing Section 4.2 co-occurrence analysis on top of the current SimpleSub without migrating. You can get (2) by adding intersection types to the constraint system incrementally. A full migration to MLstruct's Boolean algebra would give you negation types and more precise record handling, but it's a substantial rewrite of the constraint solver and canonicalization for benefits that are less immediately pressing for Nix's type system needs.

The pragmatic path is probably: implement co-occurrence simplification first (fixes `apply`), then add intersection-type overloading (fixes `+` etc.), and only consider full MLstruct if you need negation types for type narrowing or precise field tracking later.

## Sources

- [MLstruct: Principal Type Inference in a Boolean Algebra of Structural Types (OOPSLA 2022)](https://dl.acm.org/doi/10.1145/3563304)
- [The Simple Essence of Algebraic Subtyping (ICFP 2020)](https://dl.acm.org/doi/10.1145/3409006)
- [The Simple Essence of Boolean-Algebraic Subtyping (POPL 2026)](https://doi.org/10.1145/3776689)
- [MLstruct GitHub repository](https://github.com/hkust-taco/mlstruct)
- [Parreaux's blog: Demystifying MLsub](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html)
