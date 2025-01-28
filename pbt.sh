#!/usr/bin/env bash

DEFAULT_PROPTEST_CASES=50000

# allow passing in cases as arg
PROPTEST_CASES=${1:-$DEFAULT_PROPTEST_CASES}

PROPTEST_CASES=$PROPTEST_CASES cargo test --package lang --lib -- ty::check::pbt::test_type_check --exact --show-output