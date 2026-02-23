#!/usr/bin/env bash
# Type-check Nix source with tix-cli (debug build).
#
# Usage:
#   ./scripts/tixc.sh <<'EOF'          # Read from stdin
#   let x = 1; in x
#   EOF
#   ./scripts/tixc.sh test/basic.nix    # Check a local file
#   ./scripts/tixc.sh nixpkgs:lib/fixed-points.nix  # Check a nixpkgs file

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Separate tixc flags from tix-cli passthrough args.
# First non-flag argument is the input source (file path, nixpkgs: ref, or omitted for stdin).
INPUT=""
TIX_ARGS=()

for arg in "$@"; do
    if [[ -z "$INPUT" && "$arg" != -* ]]; then
        INPUT="$arg"
    else
        TIX_ARGS+=("$arg")
    fi
done

if [[ -z "$INPUT" ]]; then
    # No file argument — read from stdin.
    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT
    cat > "$tmpdir/input.nix"
    FILE="$tmpdir/input.nix"

elif [[ "$INPUT" == nixpkgs:* ]]; then
    # nixpkgs:<subpath> — resolve pinned nixpkgs and append the subpath.
    SUBPATH="${INPUT#nixpkgs:}"
    NIXPKGS_SRC="$(nix eval --raw "$REPO_ROOT"#nixpkgs-src)"
    FILE="$NIXPKGS_SRC/$SUBPATH"
    if [[ ! -f "$FILE" ]]; then
        echo "ERROR: $FILE does not exist" >&2
        exit 2
    fi

else
    # Plain file path.
    FILE="$INPUT"
    if [[ ! -f "$FILE" ]]; then
        echo "ERROR: $FILE does not exist" >&2
        exit 2
    fi
fi

cargo run --bin tix-cli -- "$FILE" "${TIX_ARGS[@]}"
