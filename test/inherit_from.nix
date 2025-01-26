let
  simple = {
    foo = 100;
  };
in
{
  inherit (simple) foo;
  a = ''test123'';
}
