# Caller for null_interp_lib.nix. Both an explicit string and the default
# must type-check.
let
  bake = import ./null_interp_lib.nix;

  result = bake { account_fallback = "stage"; };
  result_default = bake {};
in
{
  inherit result result_default;
}
