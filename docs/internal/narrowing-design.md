# Narrowing Design for Tix

## Problem Statement

Tix currently implements basic narrowing for null checks and `? attr` by creating fresh type variables per if/else branch. This is insufficient because:

- **Then-branches work**: `α_then ≤ α ∧ String` correctly narrows to `String`
- **Else-branches don't**: `α_else ≤ α` gives no useful narrowing. Without negation types, we cannot express "α_else is definitely not String"
- Real Nix code depends heavily on else-branch narrowing: `if x == null then default else x.foo` needs x to be non-null in the else branch

## Chosen Approach: Boolean-Algebraic Subtyping

We extend the existing SimpleSub-based solver with negation types, forming a full Boolean algebra of types. This is a direct extension of the MLsub lineage — not a rewrite.

### Why not other approaches?

- **Occurrence typing (Typed Racket style)**: Requires tracking logical propositions per expression. It's a checking system, not inference. Too much annotation burden.
- **Control flow analysis (TypeScript style)**: Engineering-heavy, theoretically ad-hoc, can't infer type predicates. Doesn't compose with algebraic subtyping.
- **Semantic subtyping (CDuce/Castagna style)**: The "right" answer theoretically, but changes arrow subtyping semantics. `(Int→Int) ∧ (Bool→Bool)` becomes genuinely different from `(Int∨Bool)→(Int∧Bool)`. Much more complex. We avoid this by keeping MLsub's arrow distribution and requiring annotations for overloaded functions.
- **Refinement types (Liquid types)**: Requires SMT solver. Incompatible with lightweight constraint-based inference.

### Why BAS works for us

- We already have unions and intersections — just need to add negation
- Negation on data types is simple and well-behaved
- We keep MLsub's arrow distribution (simpler solver, principal types for non-overloaded code)
- BAS has a POPL 2026 paper with soundness proof and reference implementation
- The upgrade from SimpleSub to BAS is incremental, not a rewrite

## Type Algebra Changes

Changes primarily in `lang_ty` (type representation) and `lang_check/src/constrain.rs` (subtyping).

### New type constructor

Add `Neg(TypeId)` to `Ty<R, VarType>` in `lang_ty`. Maintain the invariant that negation only appears on atoms:

```
Type ::= ...existing...
       | Neg(BaseType)        -- ¬String, ¬Null, ¬Int, etc.
       | Neg(TypeVar)         -- ¬α
```

### Normalization rules (applied eagerly)

```
¬(A ∨ B)  →  ¬A ∧ ¬B       (De Morgan)
¬(A ∧ B)  →  ¬A ∨ ¬B       (De Morgan)
¬(¬A)     →  A              (double negation elimination)
A ∧ ¬A    →  ⊥              (contradiction)
A ∨ ¬A    →  ⊤              (tautology)
```

Negation of arrows and records:
- `¬(A → B)` — doesn't arise from narrowing guards. If encountered, treat as opaque or error.
- `¬{attr: ⊤}` — means "lacks field attr". This DOES arise from `? attr` else-branches. Can be represented as a field-absence constraint rather than a full negated record type.

### Subtyping with negation

Key changes to biunification in `lang_check/src/constrain.rs` (and bounds storage in `storage.rs`):

1. When constraining `α ≤ ¬β`, propagate: α's upper bound includes ¬β
2. When constraining `¬α ≤ β`, this is equivalent to `¬β ≤ α` (contravariant flip)
3. `¬BaseType₁ ≤ ¬BaseType₂` iff `BaseType₂ ≤ BaseType₁` (contravariant)
4. `BaseType ∧ ¬BaseType` simplifies to `⊥`
5. The co-NP hardness comes from checking `A ≤ B` when both contain nested Boolean operations. In practice, narrowing produces simple patterns (one level of negation on base types).

See the sebas artifact for the full algorithm.

## Narrowing Implementation

### Phase 1: Guard Recognition (syntactic)

Add guard extraction either in `lang_ast/nameres.rs` (during name resolution) or as a separate pass in `lang_check/src/infer_expr.rs` (during the AST walk). The simpler option is doing it inline in `infer_expr.rs` when you encounter an if-expression — pattern-match on the condition node right there.

```rust
enum Guard {
    IsType(VarId, NixBaseType),  // builtins.isString x, etc.
    IsNull(VarId),                // x == null, null == x
    HasAttr(VarId, AttrName),     // x ? attr, builtins.hasAttr "attr" x
    Not(Box<Guard>),              // !(guard), for negated conditions
}
```

Recognition patterns:
- `builtins.isString <var>` → `Guard::IsType(var, String)`
- `builtins.isInt <var>` → `Guard::IsType(var, Int)`
- (same for isFloat, isBool, isAttrs, isList, isFunction, isNull, isPath)
- `<var> == null` or `null == <var>` → `Guard::IsNull(var)`
- `<var> != null` or `null != <var>` → `Guard::Not(Guard::IsNull(var))`
- `<var> ? <ident>` → `Guard::HasAttr(var, ident)`
- `builtins.hasAttr "<str>" <var>` → `Guard::HasAttr(var, str)`
- `! <guard-expr>` → `Guard::Not(inner_guard)`
- `<guard1> && <guard2>` → could be composed, but start without this
- Anything else → None (no narrowing)

### Phase 2: Constraint Generation for If-Expressions

Changes in `lang_check/src/infer_expr.rs` (the single-pass AST walk) and `lang_check/src/constrain.rs`.

Current (simplified):
```
infer(if cond then e1 else e2, env):
    infer(cond, env) ≤ Bool
    t1 = infer(e1, env)
    t2 = infer(e2, env)
    return t1 ⊔ t2
```

New:
```
infer(if cond then e1 else e2, env):
    infer(cond, env) ≤ Bool
    match extract_guard(cond):
        Some(guard) for variable x with type α in env:
            guard_type = guard_to_type(guard)  // e.g., String, Null, {attr: β}
            env_then = env[x ↦ α ∧ guard_type]
            env_else = env[x ↦ α ∧ ¬guard_type]
            t1 = infer(e1, env_then)
            t2 = infer(e2, env_else)
        None:
            t1 = infer(e1, env)
            t2 = infer(e2, env)
    return t1 ⊔ t2
```

The `env[x ↦ narrowed_type]` is environment shadowing — create a new scope where x has the narrowed type. This is similar to how let-bindings create new scopes.

### Phase 3: Record Field Narrowing

For `x ? attr`:

**Then-branch**: `x : α ∧ {attr: β_fresh}` — x definitely has the field. Accessing `x.attr` in this branch yields type `β_fresh`.

**Else-branch**: Two options for representing "x lacks field attr":

Option A (simpler): Track `absent_fields: Set<AttrName>` on record type variables. When `? attr` is false, add `attr` to the absent set. Accessing `x.attr` in the else-branch is a type error because `attr ∈ absent_fields`.

Option B (BAS-native): Use `α ∧ ¬{attr: ⊤}` as the else-branch type. This requires the subtyping algorithm to handle negated record types, but is more general.

**Recommendation**: Start with Option A. It covers the practical cases without requiring full record negation in the solver. Migrate to Option B later if needed.

### Interaction with Let-Generalization

Changes in `lang_check/src/infer.rs` (extrude/generalization) and `lang_check/src/collect.rs` (canonicalization — `OutputTy` needs a negation variant).

When generalizing `let f = x: if isString x then ... else ...`:
- The branches produce types under narrowed environments
- Branch results join via union: `type(e1) ⊔ type(e2)`
- The function type becomes `α → (type(e1) ⊔ type(e2))`
- Generalization quantifies over α as usual

This should work with existing let-generalization. Test that type variables appearing in negation positions are handled correctly during generalization (they should be — BAS's polarity rules extend SimpleSub's naturally).

## Annotations

Tix already has annotation infrastructure: `comment_parser` crate for doc comment types, `.tix` stub files, and `TypeAliasRegistry` in `lang_check/src/aliases.rs`. The narrowing work needs to extend this for annotation-based checking.

### Surface Syntax

Already supported in doc comments and `.tix` files. Union (`|`), intersection (`&`), and open records (`{ ... }`) are already parseable. No grammar changes needed for basic narrowing — the existing syntax covers the annotation cases.

### Checking Rules (new behavior needed)

When an expression has annotation T:
- For function parameters: bind the parameter at type T (no inference needed)
- For function returns: check inferred return type ≤ T
- For let-bindings: check inferred type ≤ T, use T as the binding's type in subsequent code
- For overloaded intersection types `(A₁→B₁) ∧ ... ∧ (Aₙ→Bₙ)`: check the function body against EACH component. For each `Aᵢ→Bᵢ`, type-check the body with param type `Aᵢ` and check result ≤ `Bᵢ`.

### "Annotation Required" Diagnostics

Emit when:
- Solver exceeds iteration threshold (prevents exponential blowup from co-NP cases)
- Type variable has contradictory bounds that don't simplify
- A function is used at multiple incompatible types without an annotation
- Point the diagnostic at the most specific location possible (the function definition, the ambiguous variable, etc.)

## Nix-Specific Considerations

### Why narrowing is sound in Nix

Nix is purely functional with immutable bindings. Once `x` is bound, its value never changes. There are no:
- Mutable variables (TypeScript's main narrowing invalidation source)
- Callbacks that could change state between test and use
- Aliasing concerns

Every narrowing is safe by construction. This is a major advantage over TypeScript/Flow.

### The overlay/module system escape hatch

Per Gabriella Gonzalez's "The Hard Part of Type-Checking Nix" analysis: the overlay system needs row polymorphism (which BAS can handle via field absence), but the NixOS module system's `mkOption`/`mkIf`/`mkMerge` combinators may resist static typing. Annotations serve as the escape hatch here — users annotate module option types (which `mkOption` already encourages via `type = lib.types.str`).

### Dynamic attribute access

`builtins.getAttr name set` where `name` is a runtime string cannot be narrowed. Same for `builtins.listToAttrs`. These require either annotations or being typed as returning `Any`/`⊤`.

## Key References

### Essential (read these)
1. **Parreaux, "The Simple Essence of Algebraic Subtyping" (ICFP 2020)** — The baseline algorithm tix builds on. ~500 line Scala implementation. https://dl.acm.org/doi/10.1145/3409006
2. **Chau & Parreaux, "The Simple Essence of Boolean-Algebraic Subtyping" (POPL 2026)** — Adds negation types with soundness proof. Artifact: github.com/fo5for/sebas. https://dl.acm.org/doi/10.1145/3776689
3. **Parreaux & Chau, "MLstruct" (OOPSLA 2022)** — Negation types + pattern matching in practice. Shows how to encode field absence.

### Important (skim these)
4. **Castagna et al., "On Type-Cases, Union Elimination, and Occurrence Typing" (POPL 2022)** — Proves union elimination subsumes occurrence typing. https://www.irif.fr/~gc/papers/popl22.pdf
5. **Castagna et al., "Polymorphic Type Inference for Dynamic Languages" (POPL 2024)** — State-of-the-art inference + narrowing. More ambitious than we need but good for understanding. https://dl.acm.org/doi/10.1145/3632882
6. **TypeScript PR #8010** — Anders Hejlsberg's control flow analysis. Practical engineering reference. https://github.com/Microsoft/TypeScript/pull/8010

### Background (if needed)
7. **Dolan, "Algebraic Subtyping" thesis (2017)** — The theoretical foundation for MLsub.
8. **Tobin-Hochberg & Felleisen, "Logical Types for Untyped Languages" (ICFP 2010)** — Definitive occurrence typing paper.
9. **Gonzalez, "The Hard Part of Type-Checking Nix" (2022)** — Nix-specific challenges. https://www.haskellforall.com/2022/03/the-hard-part-of-type-checking-nix.html