# Regression: hovering on `name` in `builtins.stringLength name` inside a
# `!= null` guard should show `string`, not `string | null`.
#
# The narrowing from `name != null` eliminates `null` from the type in the
# then-branch. Previously, the canonicalization of `Inter(var, ~Null)` produced
# Bottom (false contradiction), and the hover fell back to the un-narrowed type.
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
