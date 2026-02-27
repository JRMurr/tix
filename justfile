# Default recipe: list available commands
default:
    @just --list

# Build all crates
build:
    cargo build

# Run all tests
test:
    cargo test

# Run tests for a specific crate
test-crate crate:
    cargo test --package {{ crate }}

# Run property-based tests (default 50k cases)
pbt cases="50000":
    ./scripts/pbt.sh {{ cases }}

# Format code
fmt:
    cargo fmt

# Lint
clippy:
    cargo clippy

# =============================================================================
# Stub Generation
# =============================================================================

stubs_dir := "stubs/generated"

# Generate NixOS option stubs (with doc comments)
gen-stubs-nixos *args="": _ensure-stubs-dir
    cargo run --bin tix-cli -- gen-stubs nixos --descriptions -o {{ stubs_dir }}/nixos.tix {{ args }}

# Generate Home Manager option stubs (with doc comments)
gen-stubs-home-manager *args="": _ensure-stubs-dir
    cargo run --bin tix-cli -- gen-stubs home-manager --descriptions -o {{ stubs_dir }}/home-manager.tix {{ args }}

# Generate NixOS stubs from a flake's nixosConfigurations
gen-stubs-nixos-flake flake hostname="": _ensure-stubs-dir
    cargo run --bin tix-cli -- gen-stubs nixos --descriptions --flake {{ flake }} \
        {{ if hostname != "" { "--hostname " + hostname } else { "" } }} \
        -o {{ stubs_dir }}/nixos.tix

# Generate Home Manager stubs from a flake's homeConfigurations
gen-stubs-hm-flake flake username="": _ensure-stubs-dir
    cargo run --bin tix-cli -- gen-stubs home-manager --descriptions --flake {{ flake }} \
        {{ if username != "" { "--username " + username } else { "" } }} \
        -o {{ stubs_dir }}/home-manager.tix

# Generate nixpkgs top-level package stubs (for @callpackage context)
gen-stubs-pkgs *args="": _ensure-stubs-dir
    cargo run --bin tix-cli -- gen-stubs pkgs -o {{ stubs_dir }}/pkgs.tix {{ args }}

# Generate all stubs (NixOS + Home Manager + Pkgs)
gen-stubs: gen-stubs-nixos gen-stubs-home-manager gen-stubs-pkgs

_ensure-stubs-dir:
    @mkdir -p {{ stubs_dir }}

# =============================================================================
# Development
# =============================================================================

# Build and launch VS Code with tix-lsp (debug build) on a directory
code dir="test/nixos_fixture": build
    nix run .#tix-code-dev  -- {{ dir }}
