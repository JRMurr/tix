#!/usr/bin/env bash
# Type-check Nix source with tix.
#
# Usage:
#   ./scripts/tixc.sh <<'EOF'          # Read from stdin
#   let x = 1; in x
#   EOF
#   ./scripts/tixc.sh test/basic.nix    # Check a local file
#   ./scripts/tixc.sh nixpkgs:lib/fixed-points.nix  # Check a nixpkgs file
#   ./scripts/tixc.sh --release --timeout 120 --time nixpkgs:lib/strings.nix --timing

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Separate tixc flags from tix passthrough args.
# First non-flag argument is the input source (file path, nixpkgs: ref, or omitted for stdin).
INPUT=""
TIX_ARGS=()
MEM_LIMIT_GB=16
RELEASE=0
TIMEOUT=""
USE_TIME=0

ARGS=("$@")
i=0
while [[ $i -lt ${#ARGS[@]} ]]; do
    arg="${ARGS[$i]}"
    case "$arg" in
        --mem-limit)
            MEM_LIMIT_GB="${ARGS[$((i+1))]}"
            i=$((i + 2))
            ;;
        --release)
            RELEASE=1
            i=$((i + 1))
            ;;
        --timeout)
            TIMEOUT="${ARGS[$((i+1))]}"
            i=$((i + 2))
            ;;
        --time)
            USE_TIME=1
            i=$((i + 1))
            ;;
        *)
            if [[ -z "$INPUT" && "$arg" != -* ]]; then
                INPUT="$arg"
            else
                TIX_ARGS+=("$arg")
            fi
            i=$((i + 1))
            ;;
    esac
done

# Build tix first so build output doesn't mix with tix output,
# and wrappers (timeout, time, ulimit) only apply to the tix binary.
CARGO_BUILD_ARGS=(build --bin tix --manifest-path "$REPO_ROOT/Cargo.toml")
if [[ "$RELEASE" -eq 1 ]]; then
    CARGO_BUILD_ARGS+=(--release)
    TIX_CLI="$REPO_ROOT/target/release/tix"
else
    TIX_CLI="$REPO_ROOT/target/debug/tix"
fi
cargo "${CARGO_BUILD_ARGS[@]}" 2>&1

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

# Build the command with optional timeout and time wrappers.
CMD=()
if [[ -n "$TIMEOUT" ]]; then
    CMD+=(timeout "${TIMEOUT}s")
fi
if [[ "$USE_TIME" -eq 1 ]]; then
    # Use GNU time (the binary, not the shell builtin) for RSS tracking.
    GNU_TIME="$(command -v time)"
    CMD+=("$GNU_TIME" -v)
fi
CMD+=("$TIX_CLI" "$FILE" "${TIX_ARGS[@]}")

# Apply memory limit (ulimit -v takes KB; run in subshell so it only affects tix).
MEM_LIMIT_KB=$((MEM_LIMIT_GB * 1024 * 1024))
(ulimit -v "$MEM_LIMIT_KB"; exec "${CMD[@]}")
