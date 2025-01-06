let
  weird.var = 12;
  weird.other = 0;
  weird.very.nested = 0;
  weird."str key" = 10;
  # weird."interpolated ${toString weird.var}" = "why"; causes inf recursion
  weird."interpolated ${toString 1}" = "why";

  foo = {
    a.b = 1;
    # can't make this nested attr  rec b/c of the implicit above
    a = {
      other = 1;
      # other2 = a;
      #  other2 = other;
    };
    ${if weird.var == 12 then "dyn_key" else null} = {
      more.nesting = 1;
    };
    ${if weird.var == 111111111 then "won't happen" else null} = {
      other.missing.nesting = 1;
    };

    # "${toString a.b}" = "sad";
  };

  bar = rec {
    a.b = "nested";

    "${a.b}" = "why";

    ${null} = "?";
  };

in
{
  inherit foo weird bar;
  # foo.c = 1; # not allowed
  root.lower.leaf = "hi";
}
