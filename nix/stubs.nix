# ==============================================================================
# Generated Stubs Derivation (flake entry point)
# ==============================================================================
#
# Delegates to generate-stubs-runtime.nix with the flake's nixpkgs,
# home-manager, and tix inputs. This is the flake-time build path;
# runtime generation uses generate-stubs-runtime.nix directly.

{
  pkgs,
  home-manager,
  tix,
}:

import ./generate-stubs-runtime.nix {
  nixpkgs-path = pkgs.path;
  tix-path = tix;
  home-manager-path = home-manager;
  # At flake build time, these files are in the source tree rather than
  # shipped inside the tix store path.
  extract-options-nix = ../tools/extract-options.nix;
  lib-tix-path = ../stubs/lib.tix;
}
