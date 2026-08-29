#!/usr/bin/env bash

DEFAULT_CASES=50000
STUB_CASES=2000

# allow passing in cases as arg
CASES=${1:-$DEFAULT_CASES}

# Lightweight property tests (lang_ty, lsp, and lang_check's primitives,
# structural, lambda, narrowing, etc.) can handle high case counts.
HEGEL_TEST_CASES=$CASES cargo test --workspace --lib -- hegel_tests pbt:: \
    --skip pbt::stub_compose --skip pbt::let_bridged_export --skip pbt_stub_merge || exit 1

# Stub composition, cross-file polymorphism, and LSP stub-merge tests run
# full inference (with alias resolution, or twice per case) and need a lower cap.
HEGEL_TEST_CASES=$STUB_CASES cargo test --workspace --lib -- \
    pbt::stub_compose pbt::let_bridged_export pbt_stub_merge
