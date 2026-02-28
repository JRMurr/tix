{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
  # "debug" or "release" — selects the cargo build profile under target/.
  profile ? "debug",
  name ? "tix-lsp-${profile}",
}:

# Wrapper script that launches a local cargo build of tix-lsp with stubs.
# Assumes CWD is the project root (the default with direnv).
# Set TIX_ROOT to override if launching from elsewhere.
pkgs.writeShellScriptBin name ''
  root="''${TIX_ROOT:-.}"
  exec "$root/target/${profile}/tix-lsp" --stubs "$root/stubs" "$@"
''
