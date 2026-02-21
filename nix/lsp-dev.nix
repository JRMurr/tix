{
  /**
    type: pkgs :: Pkgs
  */
  pkgs
}:

# Wrapper script that launches the debug build of tix-lsp with stubs.
# Assumes CWD is the project root (the default with direnv).
# Set TIX_ROOT to override if launching from elsewhere.
pkgs.writeShellScriptBin "tix-lsp-dev" ''
  root="''${TIX_ROOT:-.}"
  exec "$root/target/debug/tix-lsp" --stubs "$root/stubs" "$@"
''
