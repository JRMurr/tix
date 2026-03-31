let
  foo =
    {
      name ? null,
    }:
    if name != null then builtins.stringLength name else 0;

  bar =
    {
      name ? null,
    }:
    if name != null then "hello ${toString name}" else "No name";

in
{
  inherit foo bar;
}
