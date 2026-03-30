# Stubs & DX

## Make narrowing guard list extensible via stubs
Type narrowing guards in `narrow.rs` are hardcoded. Proposed: add `@inline` annotation in
`.tix` stub syntax so third-party libraries can declare their own type guards.

## Improve nixpkgs lib stub coverage
~200 nixpkgs lib functions lack noogle signatures and are omitted from generated stubs.
`scripts/gen_lib_stubs.py` has manual overrides but gaps remain.

## Stub generator: fix tryEval failures and namespace doc comments
tryEval failures silently degrade types for common options (e.g. `allowedTCPPorts` should
be `[int]`). No namespace-level doc comments on intermediate fields. 92 redundant
`{ ... } | { ... }` unions. `specialisation` embeds ~90k lines inline.

## Write onboarding guide, FAQ, and error catalog
No "Adding Tix to an existing project" walkthrough, no FAQ ("Why is my type `?`?"),
no error catalog explaining each diagnostic.
