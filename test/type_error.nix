{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
}:

let

  foo = pkgs.lib.strings.concatStringsSep " ";

  bar = x: if x != null then builtins.stringLength x else 0;

  sadFoo = foo [ 1 ];

  sadBar = bar 1;

in
[
  sadFoo
  sadBar
]
