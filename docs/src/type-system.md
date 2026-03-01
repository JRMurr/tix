# Type System

Tix infers types from your code — most Nix code needs zero annotations. This page covers what types Tix understands and how they work in practice.

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

Tix understands this calling convention. Callable attrsets can be passed to higher-order functions that expect functions:

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

When a condition checks whether a variable is `null`, has a specific field, or is a particular type, tix narrows the variable's type in each branch. This prevents false errors from idiomatic guard patterns.

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

Only single-key attrpaths are supported (`x ? field`, not `x ? a.b.c`).

### Type predicate guards

All `is*` builtins are recognized as narrowing guards, whether called directly (`isString x`), qualified (`builtins.isString x`), or through a select chain (`lib.isString x`). In the then-branch, the variable is narrowed to the corresponding type. In the else-branch, the checked type is excluded:

```nix
dispatch = x:
  if isString x then builtins.stringLength x
  else if isInt x then x + 1
  else if isBool x then !x
  else null;
# each branch sees x as the appropriate type
```

Structural predicates (`isAttrs`, `isList`, `isFunction`) narrow in the then-branch only — `isAttrs x` narrows `x` to an attrset, etc. Else-branch narrowing for these is not yet supported.

### Supported narrowing conditions

- `x == null` / `null == x` / `x != null` / `null != x`
- `isNull x` / `builtins.isNull x`
- `isString x` / `builtins.isString x` / `lib.isString x` (and similarly for all `is*` builtins)
- `x ? field` / `builtins.hasAttr "field" x` — narrows x to have the field in then-branch, not have it in else-branch
- `!cond` — flips the narrowing
- `assert cond; body` — narrows in the body
- `cond1 && cond2` — both narrowings apply in the then-branch
- `cond1 || cond2` — both narrowings apply in the else-branch

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
# else-branch: x is neither string nor int
```

`&&` and `||` also apply **short-circuit narrowing** to sub-expressions. Since `a && b` only evaluates `b` when `a` is true, `b` is inferred under `a`'s then-branch narrowing:

```nix
# ||: x is non-null in the RHS (runs when x == null is false)
safe = x: x == null || x + 1 > 0;

# &&: x is non-null in the RHS (runs when x != null is true)
safe = x: x != null && isString x.name;
```

### Conditional library functions

Several nixpkgs `lib` functions take a boolean guard as their first argument and only evaluate the second argument when the guard is true. Tix recognizes these and applies narrowing to the guarded argument:

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

The detection is name-based, so `lib.strings.optionalString`, `lib.optionalString`, and a bare `optionalString` from `with lib;` are all recognized.

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

When tix can see the concrete types of the operands, it resolves the overload immediately. When the types are still polymorphic (e.g. in a generic function), resolution is deferred until more information is available.

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

Each use of `id` gets a fresh copy of the type, so `id` can be applied to both `int` and `string` without conflict.

## Recursive bindings

Tix handles recursive and mutually recursive definitions by analyzing dependency structure and inferring each group together.

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

## Unknown types (`?`)

When a binding's entire type is unconstrained, tix displays it as `?` instead of a letter:

```
craneLib :: ?              # unconstrained — entire type is unknown
id :: a -> a               # compound type — letters preserved
const :: a -> b -> a       # compound type — all params get letters
```

Lambda parameters always keep letter names since they represent genuine polymorphism. Other bindings (let, attrset fields) show `?` when their entire inferred type is a single unconstrained variable.
