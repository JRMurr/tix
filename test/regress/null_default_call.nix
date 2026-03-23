# Regression test: optional parameter with `? null` default should accept
# non-null values at call sites.
#
# This reproduces the false positive from build_tools/wrapped.nix where
# `wrap-bin` has `binaries ? null` and callers pass `binaries = ["aws"]`.
# tix incorrectly inferred `binaries` as `null` and rejected the list.
let
  # Simulate the wrap-bin pattern: a library function imported from another file.
  wrap-bin = import ./null_default_lib.nix;

  # Calling with an explicit list — this must NOT be a type error.
  result = wrap-bin {
    package = "hello";
    binaries = ["foo" "bar"];
  };

  # Calling without the optional — also fine.
  result_default = wrap-bin {
    package = "world";
  };
in
{
  inherit result result_default;
}
