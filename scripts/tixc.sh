#!/usr/bin/env bash
# Read Nix source from stdin, write to a temp file, and run tix-cli on it.
# Usage: echo 'let x = 1; in x' | ./scripts/tixc.sh

set -euo pipefail

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

cat > "$tmpdir/input.nix"

cargo run --bin tix-cli -- "$tmpdir/input.nix" "$@"
