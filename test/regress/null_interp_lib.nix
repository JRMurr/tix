# Library function with optional `? null` parameter consumed by string
# interpolation after a null guard. Same bug shape as null_tostring_lib.nix:
# `${x}` desugars to a polymorphic toString call, so the param had no
# concrete upper bound and the exported type collapsed to `null`.
{ account_fallback ? null }:
if account_fallback == null then
  ""
else
  "bucket-${account_fallback}"
