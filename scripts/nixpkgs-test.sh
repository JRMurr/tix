#!/usr/bin/env bash
#
# Run tix on nixpkgs .nix files (all or a specific subdirectory).
# Uses `tix check` for parallel inference. Symlinks nixpkgs into a tmpdir
# to avoid copying ~450MB from the read-only nix store.
#
# Usage:
#   ./scripts/nixpkgs-test.sh [OPTIONS] [DIRS...]
#
# Examples:
#   ./scripts/nixpkgs-test.sh                          # check everything
#   ./scripts/nixpkgs-test.sh pkgs/                    # just pkgs/
#   ./scripts/nixpkgs-test.sh lib/ nixos/              # lib/ and nixos/
#   ./scripts/nixpkgs-test.sh --release --timing pkgs/ # release build + timing
#   ./scripts/nixpkgs-test.sh --deadline 10            # 10s per-file deadline
#
set -euo pipefail

DEADLINE=30
JOBS=""
TIMING=0
RELEASE=0
VERBOSE=0
MEM_LIMIT_GB=16
DIRS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --deadline)
            DEADLINE="$2"
            shift 2
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
        --verbose|-v)
            VERBOSE=1
            shift
            ;;
        --mem-limit)
            MEM_LIMIT_GB="$2"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS] [DIRS...]"
            echo ""
            echo "Check nixpkgs .nix files with tix (parallel mode)."
            echo ""
            echo "Arguments:"
            echo "  DIRS...             Subdirectories to check (default: all)"
            echo "                      Examples: lib/ pkgs/ nixos/ pkgs/by-name/"
            echo ""
            echo "Options:"
            echo "  --deadline <secs>   Per-file inference deadline (default: 30)"
            echo "  --jobs, -j <N>      Number of parallel inference threads"
            echo "  --timing            Print per-phase timing and memory usage"
            echo "  --release           Build tix in release mode"
            echo "  --verbose, -v       Print file classifications"
            echo "  --mem-limit <GB>    Memory limit for tix process (default: 16)"
            echo "  --help, -h          Show this help"
            exit 0
            ;;
        -*)
            echo "Unknown flag: $1" >&2
            echo "Run '$0 --help' for usage." >&2
            exit 2
            ;;
        *)
            # Strip trailing slashes for consistency.
            DIRS+=("${1%/}")
            shift
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

if [[ ! -d "$NIXPKGS_SRC" ]]; then
    echo "ERROR: nixpkgs source not found at $NIXPKGS_SRC" >&2
    exit 2
fi

# ==============================================================================
# Set up tmpdir with symlinks into the nix store
# ==============================================================================

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

# Determine which directories to link. If none specified, link everything.
if [[ ${#DIRS[@]} -eq 0 ]]; then
    echo "Checking all of nixpkgs..."
    # Symlink every top-level entry from nixpkgs into the tmpdir.
    for entry in "$NIXPKGS_SRC"/*; do
        name="$(basename "$entry")"
        ln -s "$entry" "$TMPDIR/$name"
    done
else
    echo "Checking: ${DIRS[*]}"
    # Only symlink the requested directories. Also symlink lib/ if not
    # already included — many nixpkgs files import from ../lib.
    for dir in "${DIRS[@]}"; do
        # Support both "pkgs" and "pkgs/" and "pkgs/by-name"
        top="${dir%%/*}"
        src="$NIXPKGS_SRC/$top"
        if [[ ! -e "$src" ]]; then
            echo "WARNING: $top/ does not exist in nixpkgs, skipping" >&2
            continue
        fi
        if [[ ! -L "$TMPDIR/$top" ]]; then
            ln -s "$src" "$TMPDIR/$top"
        fi
    done
    # Always make lib/ available for imports.
    if [[ ! -L "$TMPDIR/lib" ]]; then
        ln -s "$NIXPKGS_SRC/lib" "$TMPDIR/lib"
    fi
fi

# Count .nix files that will be checked.
NIX_COUNT=$(find -L "$TMPDIR" -name '*.nix' -type f \
    ! -path '*/tests/*' \
    ! -path '*/test/*' \
    ! -path '*/deprecated/*' \
    2>/dev/null | wc -l)
echo "Found ~${NIX_COUNT} .nix files"
echo "Deadline: ${DEADLINE}s per file"

# ==============================================================================
# Generate tix.toml
# ==============================================================================

# Helper: format a bash array as a TOML array of strings.
toml_array() {
    local result="["
    local first=1
    for item in "$@"; do
        if [[ $first -eq 1 ]]; then first=0; else result+=", "; fi
        result+="\"${item}\""
    done
    result+="]"
    echo "$result"
}

EXCLUDE_PATTERNS=(
    "**/tests/**"
    "**/test/**"
    "**/deprecated/**"
    # Auto-generated giant package sets (hundreds of thousands of lines,
    # not useful to type-check). See SESSION.md.
    "**/haskell-modules/hackage-packages.nix"
    "**/lisp-modules/imported.nix"
    "**/tex/texlive/tlpdb.nix"
    "**/top-level/perl-packages.nix"
    "**/top-level/python-packages.nix"
    "**/top-level/all-packages.nix"
    "**/node-packages/node-packages.nix"
)

{
    echo "# Auto-generated for nixpkgs checking."
    echo "deadline = ${DEADLINE}"
    echo ""
    echo "[project]"
    if [[ ${#DIRS[@]} -gt 0 ]]; then
        analyze=()
        for dir in "${DIRS[@]}"; do
            analyze+=("${dir}/**/*.nix")
        done
        echo "analyze = $(toml_array "${analyze[@]}")"
    fi
    echo "exclude = $(toml_array "${EXCLUDE_PATTERNS[@]}")"
} > "$TMPDIR/tix.toml"

echo "---"
cat "$TMPDIR/tix.toml"
echo "---"

# ==============================================================================
# Run tix check
# ==============================================================================

CHECK_ARGS=(check --config "$TMPDIR/tix.toml")
if [[ -n "$JOBS" ]]; then
    CHECK_ARGS+=(-j "$JOBS")
fi
if [[ "$TIMING" -eq 1 ]]; then
    CHECK_ARGS+=(--timing)
fi
if [[ "$VERBOSE" -eq 1 ]]; then
    CHECK_ARGS+=(--verbose)
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
