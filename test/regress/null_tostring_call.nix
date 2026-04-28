# Caller for null_tostring_lib.nix. Both with and without the optional
# parameter must type-check.
let
  bake = import ./null_tostring_lib.nix;

  result = bake { modules = [ "x" ]; };
  result_default = bake {};
in
{
  inherit result result_default;
}
