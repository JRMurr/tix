let
  pkgs = import <nixpkgs> { };
  foo = pkgs.callPackage ./import { inherit pkgs; };
in
foo
