# Testing

## Add unit tests for narrow.rs guard recognition
`narrow.rs` (645 lines) has zero unit tests. Guard recognition, alias tracing, and
`MAX_ALIAS_TRACE_DEPTH` are only tested indirectly. Some existing narrowing tests only
verify crash-freedom, not inferred types.

## Add targeted test cases for untested builtins
Many builtins lack dedicated tests: `fromJSON`, `split`, `match`, `replaceStrings`, `sort`,
`partition`, `groupBy`, `mapAttrs`, `functionArgs`, `listToAttrs`, `removeAttrs`, `genList`,
`concatLists`, `concatMap`, `all`, `any`. Path interpolation has zero coverage.

## PBT: correctness tests for structural union types
Focused union PBT tests only verify primitive unions. No correctness tests for unions with
structural types like `[int] | string` or `{a: int} | null`.
