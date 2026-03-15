#!/usr/bin/env bash
#
# Run tix on all .nix files in nixpkgs lib/, classifying each result
# as pass / type-error / timeout / crash. Exits non-zero only on crashes.
#
# Usage:
#   ./scripts/nixpkgs-lib-test.sh [--timeout <secs>] [--parallel] [--jobs N] [--timing] [--release]
#
# --parallel  Copy lib/ to a temp directory, generate a tix.toml, and run
#             `tix check` for parallel inference via rayon instead of
#             checking each file sequentially in its own process.
#
set -euo pipefail

TIMEOUT=60
PARALLEL=0
JOBS=""
TIMING=0
RELEASE=0
MEM_LIMIT_GB=16

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --parallel)
            PARALLEL=1
            shift
            ;;
        --jobs|-j)
            JOBS="$2"
            shift 2
            ;;
        --timing)
            TIMING=1
            shift
            ;;
        --release)
            RELEASE=1
            shift
            ;;
        --mem-limit)
            MEM_LIMIT_GB="$2"
            shift 2
            ;;
        *)
            echo "Unknown flag: $1" >&2
            echo "Usage: $0 [--timeout <secs>] [--parallel] [--jobs N] [--timing] [--release] [--mem-limit <GB>]" >&2
            exit 2
            ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Build tix first so timing is clean.
CARGO_BUILD_ARGS=(build --bin tix --manifest-path "$REPO_ROOT/Cargo.toml")
if [[ "$RELEASE" -eq 1 ]]; then
    CARGO_BUILD_ARGS+=(--release)
    TIX_CLI="$REPO_ROOT/target/release/tix"
    echo "Building tix (release)..."
else
    TIX_CLI="$REPO_ROOT/target/debug/tix"
    echo "Building tix (debug)..."
fi
cargo "${CARGO_BUILD_ARGS[@]}" 2>&1

# Resolve pinned nixpkgs path from flake.
echo "Resolving nixpkgs path..."
NIXPKGS_SRC="$(nix eval --raw .#nixpkgs-src)"
LIB_DIR="$NIXPKGS_SRC/lib"

if [[ ! -d "$LIB_DIR" ]]; then
    echo "ERROR: $LIB_DIR does not exist" >&2
    exit 2
fi

# ==============================================================================
# Parallel mode: copy lib/ to tmpdir, generate tix.toml, run `tix check`
# ==============================================================================

if [[ "$PARALLEL" -eq 1 ]]; then
    TMPDIR="$(mktemp -d)"
    trap 'rm -rf "$TMPDIR"' EXIT

    echo "Copying $LIB_DIR → $TMPDIR/lib ..."
    cp -a "$LIB_DIR" "$TMPDIR/lib"
    # Nix store is read-only; make the copy writable so we can add tix.toml.
    chmod -R u+w "$TMPDIR/lib"

    # Generate a tix.toml that mirrors the sequential mode's exclude rules.
    cat > "$TMPDIR/lib/tix.toml" <<'TOML'
# Auto-generated for parallel nixpkgs lib/ checking.
deadline = 60

[project]
exclude = ["tests/**", "deprecated/**"]
TOML

    # Override deadline from --timeout flag.
    sed -i "s/^deadline = .*/deadline = ${TIMEOUT}/" "$TMPDIR/lib/tix.toml"

    echo "Generated $TMPDIR/lib/tix.toml"
    echo "---"

    # Build the tix check command.
    CHECK_ARGS=(check --config "$TMPDIR/lib/tix.toml" --verbose)
    if [[ -n "$JOBS" ]]; then
        CHECK_ARGS+=(-j "$JOBS")
    fi
    if [[ "$TIMING" -eq 1 ]]; then
        CHECK_ARGS+=(--timing)
    fi

    # Point at repo stubs so lib functions resolve.
    export TIX_BUILTIN_STUBS="${TIX_BUILTIN_STUBS:-$REPO_ROOT/stubs}"

    echo "Memory limit: ${MEM_LIMIT_GB} GB"
    echo "Running: tix ${CHECK_ARGS[*]}"
    echo "---"

    # tix check exits 1 on type errors (expected), only treat signals/crashes
    # (exit >= 2, excluding 1) as failures.
    # Enforce memory limit via cgroups (kernel OOM-kills on exceed, no hanging).
    set +e
    systemd-run --user --scope -q -p MemoryMax="${MEM_LIMIT_GB}G" -p MemorySwapMax=0 "$TIX_CLI" "${CHECK_ARGS[@]}"
    rc=$?
    set -e

    if [[ $rc -ge 2 ]]; then
        echo ""
        echo "tix check crashed (exit $rc)"
        exit 1
    fi

    exit 0
fi

# ==============================================================================
# Sequential mode (original behavior)
# ==============================================================================

# Collect .nix files, excluding tests/ and deprecated/ subdirectories.
mapfile -t NIX_FILES < <(
    find "$LIB_DIR" -name '*.nix' -type f \
        ! -path '*/tests/*' \
        ! -path '*/deprecated/*' \
    | sort
)

echo "Found ${#NIX_FILES[@]} .nix files in $LIB_DIR"
echo "Timeout: ${TIMEOUT}s per file"
echo "Memory limit: ${MEM_LIMIT_GB} GB"
echo "---"

pass=0
type_error=0
timed_out=0
crash=0
crash_files=()

for f in "${NIX_FILES[@]}"; do
    rel="${f#"$NIXPKGS_SRC/"}"

    # Run tix with timeout and memory limit; capture exit code.
    # Enforce memory limit via cgroups (kernel OOM-kills on exceed, no hanging).
    set +e
    systemd-run --user --scope -q -p MemoryMax="${MEM_LIMIT_GB}G" -p MemorySwapMax=0 \
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
