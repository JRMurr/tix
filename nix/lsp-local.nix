{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
  # "debug" or "release" — selects the cargo build profile under target/.
  # Required (no default): tix-lsp-dev once silently ran the release binary
  # because a defaulted profile didn't match the debug build `just code` makes.
  profile,
  name ? "tix-lsp-${profile}",
}:

# Wrapper script that launches a local cargo build of `tix lsp`.
# Assumes CWD is the project root (the default with direnv).
# Set TIX_ROOT to override if launching from elsewhere.
pkgs.writeShellScriptBin name ''
  root="''${TIX_ROOT:-.}"
  export RUST_LOG=debug
  exec "$root/target/${profile}/tix" lsp "$@"
''
