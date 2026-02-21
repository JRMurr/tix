{ crane }:
final: prev: {
  tix = (prev.callPackage ./rust.nix { inherit crane; }).binary;
}
