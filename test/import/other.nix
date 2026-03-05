{
  # type: pkgs :: Pkgs
  pkgs,
}:
let

  lib = pkgs.lib;

  res = import ./default.nix { inherit pkgs; };

in

res
