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
# add :: int -> int -> int
add = a: b: a + b;

# id :: a -> a
id = x: x;
```

Nix functions are curried — `a: b: a + b` is a function that takes `a` and returns a function that takes `b`.

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

Unions fall out naturally from the subtyping system — there's no special union syntax you need to use in your code.

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
