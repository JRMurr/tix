#!/usr/bin/env bash
# Type-check Nix source with tix (debug build).
#
# Usage:
#   ./scripts/tixc.sh <<'EOF'          # Read from stdin
#   let x = 1; in x
#   EOF
#   ./scripts/tixc.sh test/basic.nix    # Check a local file
#   ./scripts/tixc.sh nixpkgs:lib/fixed-points.nix  # Check a nixpkgs file
#   ./scripts/tixc.sh --mem-limit 8 test/basic.nix  # Limit to 8 GB RSS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Separate tixc flags from tix passthrough args.
# First non-flag argument is the input source (file path, nixpkgs: ref, or omitted for stdin).
INPUT=""
TIX_ARGS=()
MEM_LIMIT_GB=16

ARGS=("$@")
i=0
while [[ $i -lt ${#ARGS[@]} ]]; do
    arg="${ARGS[$i]}"
    if [[ "$arg" == "--mem-limit" ]]; then
        MEM_LIMIT_GB="${ARGS[$((i+1))]}"
        i=$((i + 2))
    elif [[ -z "$INPUT" && "$arg" != -* ]]; then
        INPUT="$arg"
        i=$((i + 1))
    else
        TIX_ARGS+=("$arg")
        i=$((i + 1))
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

# Point at the repo's stubs/ directory so go-to-definition works for
# lib.tix declarations during development (e.g. lib.id, mkDerivation).
export TIX_BUILTIN_STUBS="${TIX_BUILTIN_STUBS:-$REPO_ROOT/stubs}"

# Apply memory limit (ulimit -v takes KB; run in subshell so it only affects tix).
MEM_LIMIT_KB=$((MEM_LIMIT_GB * 1024 * 1024))
(ulimit -v "$MEM_LIMIT_KB"; exec cargo run --bin tix -- "$FILE" "${TIX_ARGS[@]}")
