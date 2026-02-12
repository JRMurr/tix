# Tix

A very simple/basic type checker for nix.


## High level design

The type checker uses MLsub/SimpleSub — an extension of Hindley-Milner with subtyping,
union types, and intersection types. This is based on Parreaux's
[The Simple Essence of Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html).

Key ideas:
- **Subtyping constraints** instead of equality unification: `constrain(sub, sup)` records
  directional bounds rather than merging variables.
- **Union and intersection types** emerge naturally — if-then-else with different branch
  types produces a union; function params used in multiple ways produce an intersection.
- **Level-based let-polymorphism** with `extrude` instead of `instantiate` — type variables
  at deeper levels are copied to fresh variables at the current level during reference.
- **Polarity-aware canonicalization** — variables expand to union of lower bounds in positive
  position (output) and intersection of upper bounds in negative position (input).

My "ideology" for the type checker is do as much inference as is reasonable but defer
to comments with type annotations when it would be too hard to infer.

### Pipeline

- Parse program into AST: `lang_ast/lower.rs`
- Name resolution to find variable dependencies/scopes: `lang_ast/nameres.rs`
- Group definitions by SCC (strongly connected components) for mutual recursion: `lang_ast/group_defs.rs`
- Infer types bottom-up per SCC group: `lang_check/infer.rs`

### Inference pipeline (`lang_check`)

- **Pre-allocate** TyIds for all names and expressions so recursive references work.
- **Single-pass AST walk** (`infer_expr.rs`): for each expression, infer its type and
  call `constrain(sub, sup)` inline. No separate constraint generation phase.
- **constrain** (`constrain.rs`): the core subtyping function. Records bounds on variables,
  decomposes structural types (contravariant params, covariant bodies/fields).
- **Overload resolution**: overloaded operators (`+`, `*`, etc.) are deferred until the
  SCC group is fully inferred, then resolved based on concrete bounds. Unresolved
  overloads are re-instantiated per call-site during extrusion.
- **Extrude** (`infer.rs`): copies deep-level type variables to fresh variables at the
  current level, preserving bounds via subtyping constraints. This replaces traditional
  instantiate/generalize.
- **Canonicalize** (`collect.rs`): expands the internal bounds-based representation into
  canonical `OutputTy` values with explicit Union/Intersection variants.

## links
- https://github.com/oxalica/nil
  - does some level of type inference but doest support annotations (at least for now)
  - read over its source a lot and took some code from there to get started
  - Long term would be nice to merge into their. For now re-implementing for my own understanding and ease of messing around
- https://github.com/nix-community/nixdoc stole some parsing logic from there
- [nix types rfc](https://github.com/hsjobeki/nix-types/blob/main/docs/README.md#nix-types-rfc-draft)
  - good spec for parsing doc comments
- https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf
  - An approach to hash expressions that is used here to hash our type representation
  - hashing a type makes it easy to see if two types are basically the same when they are in a union together