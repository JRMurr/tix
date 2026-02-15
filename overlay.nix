final: prev: {
  tix = (prev.callPackage ./rust.nix { }).binary;
}