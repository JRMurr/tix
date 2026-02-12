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



# Initial migration from hm to sub plan

Migrate Tix from Hindley-Milner to MLsub/SimpleSub                                                                                                                                                                                                 

Context

The current type checker uses Hindley-Milner with constraint generation + unification.
This doesn't support union types, which are needed for Nix's dynamic nature (heterogeneous
lists, if-then-else with different branch types, operator overloading). MLsub (specifically
Parreaux's SimpleSub formulation) extends HM with subtyping, union, and intersection types
while preserving principal type inference. The key change: replace equality constraints with
directional subtyping constraints tracked as bounds on type variables.

Reference: https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html

What Stays Unchanged

- lang_ast/ — parsing, lowering, name resolution, SCC grouping
- lang_ast::OverloadBinOp — still needed to identify which operators are overloaded
and look up valid type combinations
- comment_parser/ — extended but not rewritten
- cli/ — entry point
- Salsa DB, arena allocations, la-arena
- TyId pre-allocation strategy (names/exprs get TyIds upfront)
- check_file signature and InferenceResult structure
- The PBT infrastructure in pbt/mod.rs (extended, not replaced)

Key Design Decision: Separate Inference vs Output Types

Ty<R, VarType> stays unchanged — no Union/Intersection during inference. Union and
intersection types only exist in the canonical output representation. To enforce this
at the type level:

- Ty<R, VarType> — inference-time type (5 variants: TyVar, Primitive, List, Lambda, AttrSet)
- OutputTy — new standalone enum for canonical output, with 7 variants (adds Union, Intersection)
- ArcTy becomes type ArcTy = OutputTy (no longer Ty<TyRef>)
- TyRef wraps Arc<OutputTy> instead of Arc<Ty<TyRef>>

This avoids unreachable arms in every inference match and makes it impossible to
accidentally construct a union type during inference.

---
Phase 1: Split Type Representation

Files to modify

crates/lang_ty/src/lib.rs — Keep Ty<R, VarType> as-is (no changes to the enum).

crates/lang_ty/src/arc_ty.rs — Define OutputTy as a standalone enum:
pub enum OutputTy {
    TyVar(u32),
    Primitive(PrimitiveTy),
    List(OutputTyRef),
    Lambda { param: OutputTyRef, body: OutputTyRef },
    AttrSet(AttrSetTy<OutputTyRef>),
    Union(Vec<OutputTyRef>),
    Intersection(Vec<OutputTyRef>),
}
pub struct OutputTyRef(pub Arc<OutputTy>);
pub type ArcTy = OutputTy;

Move normalize_vars, free_type_vars to OutputTy. These are only needed on
canonical types anyway.

crates/lang_ty/src/attrset.rs — Change rest: Option<RefType> to open: bool.
With structural subtyping, row variables are no longer needed. open: true means
"accepts more fields" (pattern with ...), open: false means "exactly these fields".
Keep the merge method for the // operator.

crates/lang_ty/src/arbitrary.rs — Update proptest generators to use OutputTy.
Add Union/Intersection to arb_arc_ty(). Update attrset generators for open: bool.

arc_ty! macro — Rewrite to construct OutputTy variants. Add union/intersection arms.

Verification

cargo check passes. Existing tests updated for OutputTy.

---
Phase 2: Replace TypeStorage with Bounds-Based Variables

Rewrite storage.rs to track directional bounds instead of union-find equivalence classes.

crates/lang_check/src/storage.rs — complete rewrite

pub struct TypeVariable {
    pub lower_bounds: Vec<TyId>,  // types that flow INTO this var (for union)
    pub upper_bounds: Vec<TyId>,  // types this var flows INTO (for intersection)
    pub level: u32,
}

pub enum TypeEntry {
    Variable(TypeVariable),
    Concrete(Ty<TyId>),
}

pub struct TypeStorage {
    entries: Vec<TypeEntry>,  // indexed by TyId.0
    pub current_level: u32,
}

Methods: new_var(level), new_concrete(Ty<TyId>), get(TyId), get_var(TyId),
add_lower_bound(var, bound), add_upper_bound(var, bound),
enter_level(), exit_level().

Remove union-find from Cargo.toml.

crates/lang_check/src/lib.rs — update CheckCtx

- Remove TySchema, FreeVars types
- Add constrain_cache: HashSet<(TyId, TyId)> field
- Change poly_type_env: HashMap<NameId, TyId> (was HashMap<NameId, TySchema>)
- Update alloc_ty → alloc_concrete and new_var to use new storage
- Keep prim_cache (still useful)

Delete crates/lang_check/src/constraints.rs

No more ConstraintCtx, RootConstraint, DeferrableConstraint,
BinOverloadConstraint, AttrMergeConstraint, etc. The only remaining "constraint"
mechanism is constrain(sub, sup) calls. Note: OverloadBinOp itself (the enum
identifying which operators are overloaded) lives in lang_ast and is kept — it's
used to look up valid type combinations during inference.

Verification

Compiles. Tests won't pass yet (core algorithm not connected).

---
Phase 3: Implement constrain(sub, sup) Function

The core of SimpleSub. Instead of unification, records directional subtyping constraints.

New file: crates/lang_check/src/constrain.rs

impl CheckCtx<'_> {
    pub fn constrain(&mut self, sub: TyId, sup: TyId) -> Result<(), InferenceError> {
        if sub == sup { return Ok(()); }
        if !self.constrain_cache.insert((sub, sup)) { return Ok(()); }

        match (self.table.get(sub), self.table.get(sup)) {
            (Variable(_), _) => {
                self.table.add_upper_bound(sub, sup);
                for lb in self.table.get_var(sub).lower_bounds.clone() {
                    self.constrain(lb, sup)?;
                }
            }
            (_, Variable(_)) => {
                self.table.add_lower_bound(sup, sub);
                for ub in self.table.get_var(sup).upper_bounds.clone() {
                    self.constrain(sub, ub)?;
                }
            }
            (Concrete(Lambda{p1,b1}), Concrete(Lambda{p2,b2})) => {
                self.constrain(p2, p1)?;  // contravariant
                self.constrain(b1, b2)?;  // covariant
            }
            (Concrete(List(e1)), Concrete(List(e2))) => {
                self.constrain(e1, e2)?;
            }
            (Concrete(AttrSet(a1)), Concrete(AttrSet(a2))) => {
                for (key, sup_field) in &a2.fields {
                    match a1.fields.get(key) {
                        Some(sub_field) => self.constrain(*sub_field, *sup_field)?,
                        None => return Err(InferenceError::MissingField(..)),
                    }
                }
            }
            (Concrete(Primitive(p1)), Concrete(Primitive(p2))) if p1 == p2 => Ok(()),
            _ => Err(InferenceError::TypeMismatch(..)),
        }
    }
}

PBT for constrain

- constrain(a, a) always succeeds (reflexivity)
- If constrain(a, b) and constrain(b, c) succeed, constrain(a, c) succeeds (transitivity)
- constrain({a: int, b: string}, {a: int}) succeeds (width subtyping)
- constrain({a: int}, {a: int, b: string}) fails (missing field)
- constrain(int, string) fails
- constrain(a -> b, c -> d) implies constrain(c, a) and constrain(b, d) (contravariance)

Verification

Unit tests on constrain in isolation pass.

---
Phase 4: Single-Pass AST Inference

Replace the two-phase generate+solve with a single-pass walker that calls constrain inline.

New file: crates/lang_check/src/infer_expr.rs (replaces generate.rs)

Key expression handlers:

Literals — allocate concrete type, return it.

References — look up in poly_type_env; if found, extrude to instantiate.
Otherwise return pre-allocated TyId for the name.

Lambda — fresh var for param, infer body, return Lambda { param, body }.

Apply — infer fun and arg, create fresh return var, constrain(fun, Lambda{arg, ret}).

if-then-else — constrain cond to Bool. Create result var. Constrain both branches
as lower bounds of result: constrain(then_ty, result) and constrain(else_ty, result).
This naturally produces union types when branches differ.

List — create elem var, constrain each element as lower bound of elem var.
Heterogeneous lists get [int | string | ...].

AttrSet — infer each field, return AttrSet { fields, open: false }.

Select (x.foo) — create result var, constrain x against AttrSet({ foo: result, open: true }).

LetIn — enter_level(), infer bindings, exit_level(), infer body.

BinOp (overloaded) — pragmatic approach: check if both arg types have concrete
lower bounds, if so pick the right overload directly. Otherwise keep a small pending
list re-checked after SCC group inference. (Full intersection-type-based overloading
is a future enhancement.)

BinOp (non-overloaded) — same logic as current: bool ops constrain both sides to
Bool, comparison ops return Bool, list concat constrains both to same list type.

Implement extrude (replaces instantiate)

fn extrude(&mut self, ty_id: TyId, polarity: bool) -> TyId {
    match self.table.get(ty_id) {
        Variable(v) if v.level > self.table.current_level => {
            let fresh = self.new_var();
            if polarity {
                self.constrain(ty_id, fresh)?;  // fresh ≥ original
            } else {
                self.constrain(fresh, ty_id)?;  // fresh ≤ original
            }
            fresh
        }
        Variable(_) => ty_id,
        Concrete(Lambda { param, body }) => {
            let p = self.extrude(param, !polarity);  // flip
            let b = self.extrude(body, polarity);
            self.alloc_concrete(Ty::Lambda { param: p, body: b })
        }
        Concrete(List(e)) => {
            let e2 = self.extrude(e, polarity);
            self.alloc_concrete(Ty::List(e2))
        }
        Concrete(AttrSet(a)) => {
            // extrude each field
            ...
        }
        Concrete(Primitive(_)) => ty_id,
    }
}

Rewrite crates/lang_check/src/infer.rs

- infer_prog: keep pre-allocation, iterate SCC groups, call infer_scc_group
- infer_scc_group: enter_level(), infer all definitions, exit_level(),
record names in poly_type_env (the TyId itself; level marks it as polymorphic)
- infer_root: infer entry expression
- Remove generalize, instantiate, instantiate_ty, instantiate_constraint
- Remove all TySchema usage

Delete old files

- crates/lang_check/src/generate.rs — replaced by infer_expr.rs
- crates/lang_check/src/solve.rs — replaced by constrain.rs

Verification

Port the 15 existing unit tests. Expected type changes:
- if true then 1 else "hi" → int | string (was: type error)
- [1 "hi"] → [int | string] (was: type error)
- add = a: b: a + b → overloaded type (pending operator mechanism)
- Row-poly tests → now use width subtyping (no rest variable)
- Let-generalization tests → same behavior, different mechanism

---
Phase 5: Update Canonicalization

Rewrite crates/lang_check/src/collect.rs

Polarity-aware expansion of type variables:
- Positive position (output): variable → union of lower bounds
- Negative position (input): variable → intersection of upper bounds
- Lambda param flips polarity
- Cycle detection via cache sentinel

Simplification: flatten nested unions/intersections, deduplicate members,
collapse single-member unions/intersections.

Verification

All unit tests produce expected ArcTy output.

---
Phase 6: Update Comment Parser for | and &

crates/comment_parser/src/comment.pest

Add union and intersection syntax between arrow and atom levels:

type_expr     = { arrow_segment ~ ("->" ~ arrow_segment)* }
arrow_segment = { union_type }
union_type    = { isect_type ~ ("|" ~ isect_type)* }
isect_type    = { atom_type ~ ("&" ~ atom_type)* }
atom_type     = { paren_type | list_type | type_ref }

Precedence: -> (lowest) > | > & > atoms (highest).

crates/comment_parser/src/collect.rs

Add Rule::union_type and Rule::isect_type handlers. Since Ty<R> doesn't have
Union/Intersection, the comment parser needs its own output type for parsed annotations.
Options:
1. Use OutputTy directly (slightly odd since it's an "output" type used as parser output)
2. Keep KnownTy = Ty<KnownTyRef, TypeVarValue> and add Union/Intersection to Ty
just for parsing (contradicts the split)
3. Define a small ParsedTy enum in comment_parser that includes union/intersection

Option 3 is cleanest. Define ParsedTy in comment_parser with all variants including
Union/Intersection. The intern_known_ty function in lang_check converts ParsedTy
to internal TyId representations (union annotations become constraints during checking).

crates/lang_check/src/lib.rs

Update intern_know_ty_inner to handle ParsedTy::Union and ParsedTy::Intersection.
For union annotations: create a fresh variable with each union member as a lower bound.
For intersection annotations: create a fresh variable with each member as an upper bound.

Verification

Parser tests: int | string, (int -> int) & (string -> string),
(int | string) -> bool.

---
Phase 7: Extend PBT Tests

crates/lang_check/src/pbt/mod.rs

New generators:
- if_then_else_strat: pick two different primitive types, generate
if true then <expr1> else <expr2>, expect Union([ty1, ty2])
- heterogeneous_list_strat: generate lists with mixed element types,
expect List(Union([...]))
- record_subtyping_strat: generate (x: x.field) { field = val; extra = ... },
expect the field's type

New property tests:
- Subtyping reflexivity: for any generated type, constrain(t, t) succeeds
- Width subtyping: for any attrset, removing a field produces a supertype
- If-then-else produces union: result type contains both branch types

crates/lang_ty/src/arbitrary.rs

Add Union and Intersection to arb_arc_ty() recursive generator.
Add open field to attrset generator.

Verification

cargo test — all unit tests and PBT pass. Run PBT with higher case count
via existing pbt.sh script.

---
Phase 8: Cleanup

- Remove commented-out code throughout lang_check
- Remove union-find dependency from Cargo.toml
- Update README.md high-level design section
- Update InferenceError enum — remove unification-specific variants,
add TypeMismatch, MissingField, NotAFunction
- Add notes to SESSION.md for future work: full intersection-type overloading,
type narrowing/flow typing, literal types, with expression support

---
Summary of File Changes
┌─────────────────────────────────┬───────────────────────────────────────────────────────┐
│              File               │                        Action                         │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_ty/src/lib.rs              │ Keep Ty unchanged; minor updates for open: bool       │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_ty/src/arc_ty.rs           │ Rewrite — define OutputTy with Union/Intersection     │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_ty/src/attrset.rs          │ Modify — rest → open: bool                            │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_ty/src/arbitrary.rs        │ Modify — extend generators for OutputTy               │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/storage.rs       │ Rewrite — bounds-based variables                      │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/lib.rs           │ Modify — remove TySchema, update CheckCtx             │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/infer.rs         │ Rewrite — level-based generalization, extrude         │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/infer_expr.rs    │ New — single-pass AST inference                       │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/constrain.rs     │ New — core constrain(sub, sup)                        │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/collect.rs       │ Rewrite — polarity-aware canonicalization to OutputTy │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/generate.rs      │ Delete                                                │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/solve.rs         │ Delete                                                │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/constraints.rs   │ Delete                                                │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/tests.rs         │ Modify — update expectations, add new tests           │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ lang_check/src/pbt/mod.rs       │ Modify — extend generators and properties             │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ comment_parser/src/comment.pest │ Modify — add | and &                                  │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ comment_parser/src/collect.rs   │ Modify — handle union/intersection rules              │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ comment_parser/src/lib.rs       │ Modify — define ParsedTy or update KnownTy            │
├─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ README.md                       │ Modify — update design docs                           │
└─────────────────────────────────┴───────────────────────────────────────────────────────┘
Future Work (not in scope)

- Full intersection-type-based operator overloading (replace pragmatic pending list)
- Type narrowing / flow-sensitive typing (TypeScript-style discriminated unions)
- Literal / singleton types ("circle" as a type, not just string)
- with expression support
- Type simplification (co-occurrence analysis, variable merging — Parreaux Section 5)
╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌