#!/usr/bin/env bash

DEFAULT_PROPTEST_CASES=50000
STUB_PROPTEST_CASES=2000

# allow passing in cases as arg
PROPTEST_CASES=${1:-$DEFAULT_PROPTEST_CASES}

# Both frameworks read their case count from the environment. (Note: the
# lang_check proptest blocks set `cases:` explicitly, which overrides
# PROPTEST_CASES — see SESSION.md.)
export HEGEL_TEST_CASES=$PROPTEST_CASES

# Hegel property tests outside lang_check (lang_ty, lsp).
cargo test --package lang_ty --package tix-lsp --lib -- hegel_tests || exit 1

# Lightweight PBT tests (primitives, structural, lambda, narrowing, etc.)
# can handle high case counts. Excludes the multi-file modules which run
# full inference multiple times per case and need a lower cap (below).
PROPTEST_CASES=$PROPTEST_CASES cargo test --package lang_check --lib -- pbt:: hegel_tests \
    --skip pbt::let_bridged_export --skip pbt::stub_compose --show-output || exit 1

# Stub composition tests run full type inference with alias resolution per case,
# so they need a lower case count.
PROPTEST_CASES=$STUB_PROPTEST_CASES HEGEL_TEST_CASES=$STUB_PROPTEST_CASES \
    cargo test --package lang_check --lib -- pbt::stub_compose --show-output || exit 1

# Cross-file polymorphism tests run two full inferences (single-file + multi-file)
# per case, so they share the stub-compose case budget.
PROPTEST_CASES=$STUB_PROPTEST_CASES HEGEL_TEST_CASES=$STUB_PROPTEST_CASES \
    cargo test --package lang_check --lib -- pbt::let_bridged_export --show-output
