{
  pkgs,
  # String path to the LSP server binary. Allows callers to provide either a
  # nix store path (release) or a dev wrapper script (debug build).
  serverPath,
  name ? "tix-code",
}:

let
  # VSCodium bundled with the Nix IDE extension. User settings are injected
  # separately via a wrapper script (vscode-with-extensions only handles
  # extensions, not settings).
  codiumWithExt = pkgs.vscode-with-extensions.override {
    vscode = pkgs.vscodium;
    vscodeExtensions = [
      pkgs.vscode-extensions.jnoortheen.nix-ide
    ];
  };
in

# Wrapper that launches VSCodium with an isolated user-data directory so it
# doesn't interfere with the user's normal profile.
#
# The server wrapper script is written at launch time (not baked into the nix
# store) so it can capture TIX_ROOT from the calling shell. This matters for
# tix-code-dev where tix-lsp-dev resolves the debug binary relative to
# TIX_ROOT (defaulting to CWD). Without this, VSCodium would spawn tix-lsp-dev
# with CWD set to the opened project directory, not the tix source tree.
pkgs.writeShellScriptBin name ''
  data_dir="''${XDG_DATA_HOME:-$HOME/.local/share}/tix-code"
  settings_dir="$data_dir/User"
  mkdir -p "$settings_dir"

  # Write a server wrapper that freezes TIX_ROOT to the current value (or PWD)
  # so the LSP can find the debug binary regardless of VSCodium's CWD.
  cat > "$data_dir/tix-lsp-wrapper" <<WRAPPER
  #!/bin/sh
  export TIX_ROOT="''${TIX_ROOT:-$PWD}"
  exec ${serverPath} "\$@"
  WRAPPER
  chmod +x "$data_dir/tix-lsp-wrapper"

  cat > "$settings_dir/settings.json" <<SETTINGS
  ${builtins.toJSON {
    "nix.enableLanguageServer" = true;
    "nix.serverPath" = "$data_dir/tix-lsp-wrapper";
  }}
  SETTINGS

  exec "${codiumWithExt}/bin/codium" \
    --user-data-dir "$data_dir" \
    "$@"
''
