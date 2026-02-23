#!/usr/bin/env bash
#
# Run tix-cli on all .nix files in nixpkgs lib/, classifying each result
# as pass / type-error / timeout / crash. Exits non-zero only on crashes.
#
# Usage:
#   ./scripts/nixpkgs-lib-test.sh [--timeout <secs>]
#
set -euo pipefail

TIMEOUT=60

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        *)
            echo "Unknown flag: $1" >&2
            echo "Usage: $0 [--timeout <secs>]" >&2
            exit 2
            ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Build tix-cli first so timing is clean.
echo "Building tix-cli..."
cargo build --bin tix-cli --manifest-path "$REPO_ROOT/Cargo.toml" 2>&1
TIX_CLI="$REPO_ROOT/target/debug/tix-cli"

# Resolve pinned nixpkgs path from flake.
echo "Resolving nixpkgs path..."
NIXPKGS_SRC="$(nix eval --raw .#nixpkgs-src)"
LIB_DIR="$NIXPKGS_SRC/lib"

if [[ ! -d "$LIB_DIR" ]]; then
    echo "ERROR: $LIB_DIR does not exist" >&2
    exit 2
fi

# Collect .nix files, excluding tests/ and deprecated/ subdirectories.
mapfile -t NIX_FILES < <(
    find "$LIB_DIR" -name '*.nix' -type f \
        ! -path '*/tests/*' \
        ! -path '*/deprecated/*' \
    | sort
)

echo "Found ${#NIX_FILES[@]} .nix files in $LIB_DIR"
echo "Timeout: ${TIMEOUT}s per file"
echo "---"

pass=0
type_error=0
timed_out=0
crash=0
crash_files=()

for f in "${NIX_FILES[@]}"; do
    rel="${f#"$NIXPKGS_SRC/"}"

    # Run tix-cli with timeout; capture exit code.
    set +e
    timeout "${TIMEOUT}s" "$TIX_CLI" "$f" >/dev/null 2>&1
    rc=$?
    set -e

    case $rc in
        0)
            printf "  PASS      %s\n" "$rel"
            pass=$((pass + 1))
            ;;
        1)
            printf "  TYPE_ERR  %s\n" "$rel"
            type_error=$((type_error + 1))
            ;;
        124)
            printf "  TIMEOUT   %s\n" "$rel"
            timed_out=$((timed_out + 1))
            ;;
        *)
            printf "  CRASH(%d) %s\n" "$rc" "$rel"
            crash=$((crash + 1))
            crash_files+=("$rel (exit $rc)")
            ;;
    esac
done

# Summary table.
echo ""
echo "=============================="
echo " Summary"
echo "=============================="
printf "  Pass:       %d\n" "$pass"
printf "  Type error: %d\n" "$type_error"
printf "  Timeout:    %d\n" "$timed_out"
printf "  Crash:      %d\n" "$crash"
echo "------------------------------"
printf "  Total:      %d\n" "${#NIX_FILES[@]}"
echo "=============================="

if [[ $crash -gt 0 ]]; then
    echo ""
    echo "CRASHED FILES:"
    for cf in "${crash_files[@]}"; do
        echo "  - $cf"
    done
    exit 1
fi

echo ""
echo "No crashes detected."
exit 0
