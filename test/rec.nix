let
  simple = {
    foo = 100;
  };
in
rec {
  inherit (simple) foo;
  a = 1;

  b =
    let
      x = 5;
    in
    a + x + foo;
}
