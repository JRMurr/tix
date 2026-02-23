#!/usr/bin/env bash

DEFAULT_PROPTEST_CASES=50000
STUB_PROPTEST_CASES=2000

# allow passing in cases as arg
PROPTEST_CASES=${1:-$DEFAULT_PROPTEST_CASES}

# Lightweight PBT tests (primitives, structural, lambda, narrowing, etc.)
# can handle high case counts.
PROPTEST_CASES=$PROPTEST_CASES cargo test --package lang_check --lib -- "pbt::test_" --show-output || exit 1

# Stub composition tests run full type inference with alias resolution per case,
# so they need a lower case count.
PROPTEST_CASES=$STUB_PROPTEST_CASES cargo test --package lang_check --lib -- pbt::stub_compose --show-output
