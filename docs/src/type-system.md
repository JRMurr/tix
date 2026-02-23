# Type System

**TLDR:** Tix uses MLsub/SimpleSub — Hindley-Milner with subtyping. You get principal type inference with union and intersection types. Most code needs zero annotations.

## Primitives

| Type | Nix values |
|------|-----------|
| `int` | `1`, `42`, `-3` |
| `float` | `3.14`, `1.0` |
| `string` | `"hello"`, `''multi-line''` |
| `bool` | `true`, `false` |
| `path` | `./foo`, `/nix/store/...` |
| `null` | `null` |

## Functions

Functions are inferred from usage. The parameter type comes from how it's used in the body, and the return type is whatever the body produces.

```nix
# id :: a -> a
id = x: x;

# apply :: (a -> b) -> a -> b
apply = f: x: f x;

# negate :: bool -> bool
negate = x: !x;
```

Nix functions are curried — `f: x: f x` is a function that takes `f` and returns a function that takes `x`.

### Callable attrsets (`__functor`)

In Nix, an attrset with a `__functor` field can be called as a function. The `__functor` field must be a function that takes the attrset itself (`self`) as its first argument, followed by the actual parameter:

```nix
let
  counter = {
    __functor = self: x: self.base + x;
    base = 10;
  };
in counter 5  # 15
```

Tix understands this calling convention. When an attrset with `__functor` flows into a function position, tix constrains `__functor` as `self -> (param -> result)` where `self` is the attrset itself. This means callable attrsets can be passed to higher-order functions that expect functions:

```nix
let
  apply = f: f 1;
  obj = { __functor = self: x: x + 1; };
in apply obj  # 2
```

## Union types

When an expression can produce different types, tix infers a union.

```nix
# if-then-else with different branches
x = if cond then 1 else "fallback";
# x :: int | string

# heterogeneous lists
xs = [ 1 "two" null ];
# xs :: [int | string | null]
```

Unlike Rust enums or Haskell sum types, unions don't need to be declared upfront — they're inferred automatically from the code.

## Type narrowing

When a condition checks whether a variable is `null` or has a specific field, tix narrows the variable's type in each branch. This prevents false errors from idiomatic guard patterns.

### Null guards

```nix
getName = drv:
  if drv == null then "<none>"
  else drv.name;
# getName :: { name: a, ... } -> a | string
# drv is null in then-branch, non-null in else-branch
```

### HasAttr (`?`) guards

```nix
getField = arg:
  if arg ? escaped then arg.escaped
  else if arg ? unescaped then arg.unescaped
  else null;
# each branch narrows arg to have the checked field
```

In the then-branch, tix creates a fresh variable constrained to have the checked field. This prevents field access errors from cross-branch constraint contamination. Only single-key attrpaths are supported (`x ? field`, not `x ? a.b.c`).

### Type predicate guards

All `is*` builtins are recognized as narrowing guards, whether called directly (`isString x`), qualified (`builtins.isString x`), or through a select chain (`lib.types.isString x`, `lib.isAttrs x`). In the then-branch, the variable is narrowed to the corresponding primitive type. In the else-branch, a negation type (`~T`) is added to exclude the checked type:

```nix
dispatch = x:
  if isString x then builtins.stringLength x
  else if isInt x then x + 1
  else if isBool x then !x
  else null;
# in the else-branch of isString, x has type a & ~string
```

### Supported narrowing conditions

- `x == null` / `null == x` / `x != null` / `null != x`
- `isNull x` / `builtins.isNull x`
- `isString x` / `builtins.isString x` / `lib.types.isString x`
- `isInt x` / `builtins.isInt x` / `lib.isInt x`
- `isFloat x` / `builtins.isFloat x` / `lib.isFloat x`
- `isBool x` / `builtins.isBool x` / `lib.isBool x`
- `isPath x` / `builtins.isPath x` / `lib.isPath x`
- `isAttrs x` / `builtins.isAttrs x` / `lib.isAttrs x` (then-branch only)
- `isList x` / `builtins.isList x` / `lib.isList x` (then-branch only)
- `isFunction x` / `builtins.isFunction x` / `lib.isFunction x` (then-branch only)
- `x ? field` / `builtins.hasAttr "field" x` (then-branch narrows x to have the field; else-branch narrows x to not have the field)
- `!cond` (flips the narrowing)
- `assert cond; body` (narrows in the body)
- `cond1 && cond2` (both narrowings apply in the then-branch)
- `cond1 || cond2` (both narrowings apply in the else-branch)

### Boolean combinators

`&&` and `||` combine multiple narrowing conditions:

```nix
# &&: both guards hold in the then-branch
safeGet = x:
  if x != null && x ? name then x.name
  else "default";
# then-branch: x is non-null AND has field `name`

# ||: both guards fail in the else-branch
dispatch = x:
  if isString x || isInt x then doSomething x
  else x;
# else-branch: x is neither string nor int (has ~string & ~int)
```

For `&&`, only the then-branch gets combined narrowings (we can't determine which guard failed in the else-branch). For `||`, only the else-branch gets combined narrowings (we can't determine which guard holds in the then-branch).

Additionally, `&&` and `||` apply **short-circuit narrowing** to sub-expressions: since `a && b` only evaluates `b` when `a` is true, `b` is inferred under `a`'s then-branch narrowing. Similarly, `a || b` infers `b` under `a`'s else-branch narrowing:

```nix
# ||: x is non-null in the RHS (runs when x == null is false)
safe = x: x == null || x + 1 > 0;

# &&: x is non-null in the RHS (runs when x != null is true)
safe = x: x != null && isString x.name;
```

### Conditional library functions

Several nixpkgs `lib` functions take a boolean guard as their first argument and only evaluate the second argument when the guard is true. Tix recognizes these by name and applies then-branch narrowing to the guarded argument:

```nix
{ x }:
let
  # x.name is safe — tix narrows x to non-null in the second argument
  name = lib.optionalString (x != null) x.name;
in name
```

Recognized functions:
- `lib.optionalString` / `lib.strings.optionalString`
- `lib.optionalAttrs` / `lib.attrsets.optionalAttrs`
- `lib.optional` / `lib.lists.optional`
- `lib.mkIf`

These work with any narrowing guard — null checks, `isString`, `? field`, etc. The detection is name-based (the leaf segment of the attribute path), so `lib.strings.optionalString`, `lib.optionalString`, and a bare `optionalString` from `with lib;` are all recognized.

### Negation normalization

Negation types are normalized during canonicalization using standard Boolean algebra rules:

- **Double negation**: `~~T` simplifies to `T`
- **De Morgan (union)**: `~(A | B)` becomes `~A & ~B`
- **De Morgan (intersection)**: `~(A & B)` becomes `~A | ~B`
- **Contradiction**: `T & ~T` or `string & int` in an intersection is detected as uninhabited and displayed as `never`
- **Tautology**: `T | ~T` in a union is detected as universal and simplifies to `any` (the top type — every value inhabits it)
- **Redundant negation**: `{name: string} & ~null` simplifies to `{name: string}` (attrsets are inherently non-null)
- **Union absorption**: `{...} | {x: int, ...}` simplifies to `{...}` — an open attrset with fewer required fields subsumes more specific open attrsets in a union
- **Intersection factoring**: `(A | C) & (B | C)` simplifies to `C | (A & B)` — shared members across all union terms in an intersection are factored out using the distributive law

These rules keep inferred types readable and prevent redundant negations from accumulating through nested guards.

### How narrowing works internally

Narrowing uses first-class intersection types during inference (following the MLstruct approach from OOPSLA 2022). When `isString x` is the condition:

- **Then-branch**: x gets type `α ∧ string` (an intersection of the original type variable with string)
- **Else-branch**: x gets type `α ∧ ~string` (intersection with negation)

These intersection types are structural — they flow through constraints, extrusion, and generalization like any other type. This means narrowing information survives let-polymorphism:

```nix
let f = x: if isNull x then 0 else x; in f
# f :: a -> int | ~null
# The ~null constraint on the else-branch's x is preserved
```

When a narrowed type like `α ∧ ~null` flows into a function that expects `string`, the solver applies variable isolation (the "annoying" constraint decomposition from MLstruct): `α ∧ ~null <: string` becomes `α <: string | null`, correctly constraining α without losing the negation information.

## Row polymorphism (open attrsets)

Functions that access attrset fields get inferred types that are open — they accept any attrset that has the required fields.

```nix
# getName :: { name: a, ... } -> a
getName = x: x.name;

# works on any attrset with a `name` field
getName { name = "alice"; age = 30; }  # "alice"
getName { name = 42; extra = true; }   # 42
```

The `...` in the inferred type means "and maybe other fields." This is how Nix's pattern destructuring works too:

```nix
# greet :: { name: string, ... } -> string
greet = { name, ... }: "hello ${name}";
```

## Optional fields (pattern defaults)

When a lambda pattern has fields with defaults (`? value`), those fields are marked as optional in the inferred type. Callers can omit optional fields without triggering a missing-field error.

```nix
# mkGreeting :: { name: string, greeting?: string } -> string
mkGreeting = { name, greeting ? "hello" }: "${greeting} ${name}";

mkGreeting { name = "alice"; }                    # "hello alice"
mkGreeting { name = "bob"; greeting = "hey"; }    # "hey bob"
```

Optional fields are shown with a `?` suffix in the inferred type. Required fields (no default) still produce an error if omitted:

```nix
# This is fine — `y` is optional:
({ x, y ? 0 }: x + y) { x = 1; }    # 1

# This errors — `y` is required:
({ x, y }: x + y) { x = 1; }         # error: missing field `y`
```

## Attrset merge (`//`)

The merge operator produces a type that combines both sides. The right side wins for overlapping fields.

```nix
base = { a = 1; b = "two"; };
override = { b = 3; c = true; };
merged = base // override;
# merged :: { a: int, b: int, c: bool }
```

## Operator overloading

`+` is overloaded across several types:

| Left | Right | Result |
|------|-------|--------|
| `int` | `int` | `int` |
| `float` | `float` | `float` |
| `string` | `string` | `string` |
| `path` | `path` | `path` |
| `path` | `string` | `path` |
| `string` | `path` | `string` |

Other arithmetic operators (`-`, `*`, `/`) work on `int` and `float`.

When tix can see the concrete types of the operands, it resolves the overload immediately. When the types are still variables (e.g. in a polymorphic function), resolution is deferred until more information is available.

## Let polymorphism

Bindings introduced with `let` are generalized — they can be used at different types in the body.

```nix
let
  id = x: x;
in {
  a = id 1;       # int
  b = id "hello";  # string
}
```

Each use of `id` gets a fresh copy of the type via extrusion (SimpleSub's replacement for traditional instantiate/generalize).

## Recursive bindings

Tix handles recursive and mutually recursive definitions by grouping them into SCCs (strongly connected components) and inferring each group together.

```nix
let
  fib = n: if n < 2 then n else fib (n - 1) + fib (n - 2);
in fib 10
# fib :: int -> int
```

## Builtins

Tix knows the types of ~75 Nix builtins. Some examples:

```
builtins.map       :: (a -> b) -> [a] -> [b]
builtins.filter    :: (a -> bool) -> [a] -> [a]
builtins.head      :: [a] -> a
builtins.attrNames :: { ... } -> [string]
builtins.length    :: [a] -> int
builtins.typeOf    :: a -> string
```

Unknown builtins get a fresh type variable — they won't cause errors, but they won't provide type information either.
