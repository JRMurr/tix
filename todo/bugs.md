# Bugs

## resolve_to_concrete_id picks arbitrary lower bound [high]
Variable with `[Int, String]` lower bounds resolves to `Int`, silently losing `String`.
`type_table.rs:161-181` returns the first concrete bound found. A previous fix was reverted
because it regressed extrusion (wrapper_foldl_int_and_list test).

## Null-default field loses polymorphic return type
`let f = { config ? null }: config; in f {}` displays as `{ config?: a } -> null`
instead of `{ config?: a } -> (a | null)`. Interaction between optional-field default
handling and extrusion.

## Carry merge constraints across SCC group boundaries
Polymorphic `//` merge constraints are discarded at SCC group end. `let f = a: b: (a // b).z;
in f { x = 1; } { y = 2; }` does NOT error because the merge never resolves.

## Chained || null guard narrowing error
`a == null || b == null || c == null` produces a `~null` vs `null` error in the rightmost
operand. Left-associative `||` applies else-branch narrowing from compound LHS to RHS.

## Overloaded operators don't survive file boundaries
`+` in `a: b: a + b` loses overload context across the OutputTy boundary between files.
Exported type shows as `? -> ? -> ?` instead of retaining concrete types.
