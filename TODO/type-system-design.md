# Type System Design

## Recursive function narrowing false positives
Recursive functions with `isFunction`/`isAttrs`/`isList` narrowing on the same parameter
produce false positives. SCC-level inference shares a single type variable across all call
sites including recursive calls. Fix requires per-call-site flow sensitivity.

## Literal/singleton types for discriminated unions
`"circle"` is `string`, not `"circle"`. No TypeScript-style discriminated unions. Blocks
NixOS enum options, string-keyed dispatch, tagged union idioms in nixpkgs.

## Model Nix overlays in the type system
Overlays are the primary composition mechanism in real Nix codebases. `final`/`prev`
parameters are `?`, overlay-injected packages don't appear in `Pkgs` type.

## Model NixOS module system (options/config duality)
`mkOption`, `mkEnableOption`, `types.submodule` etc. are not modeled. The
`options.foo.enable` -> `config.foo.enable` duality isn't captured. Arguably the most
important typing relationship in NixOS.

## Intersection annotation body verification
Per-component verification of intersection-of-function annotations is deferred.
`(int -> int) & (string -> string)` is accepted as store-and-trust. The body is not
checked against each component separately.

## Multi-key attrpath narrowing
Only single-key `x ? field` narrowing works. Multi-segment `x ? foo.bar.baz` silently
fails to narrow.

## Else-branch narrowing for compound types
`isAttrs`/`isList`/`isFunction` guards only narrow the then-branch. No `¬{..}` / `¬[..]` /
`¬(→)` representation for else-branch narrowing.

## Resolve angle-bracket imports (<nixpkgs>)
`<nixpkgs>` is silently skipped during import resolution. Users get `?` with no guidance.
Common in older-style Nix code.

## Parameterized type aliases in .tix files
`type Overridable<T> = T | T -> T` would reduce duplication in stubs. Currently type
aliases can't take parameters. Workaround is manual expansion.

## Intersection-type-based operator overloading
Alternative to deferred overload resolution: type `+` as
`(int -> int -> int) & (string -> string -> string) & (float -> float -> float)`.
More principled but needs design work.
