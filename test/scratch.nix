let
  foo = { }@arg: arg.bar;
in
foo { bar = 1; } # type errors
# foo { } # does not type error
