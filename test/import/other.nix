{
  # type: pkgs :: Pkgs
  pkgs,
}:
let

  lib = pkgs.lib;

  res = import ./barrel.nix { inherit pkgs; };

in

res.hello
