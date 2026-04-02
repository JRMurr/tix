{
  # type: pkgs :: Pkgs
  pkgs,
}:
let

  res = import ./default.nix { inherit pkgs; };

in

res
