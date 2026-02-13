{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
}:

let 

  foo = pkgs.lib.strings.concatStringsSep " ";


  x = foo [""];

in

foo [1];