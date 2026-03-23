# Library function with optional parameter defaulting to null.
# Simulates wrap-bin from build_tools/nixlib/wrap-bin.nix.
{ package, binaries ? null }:
  if binaries == null then
    package
  else
    builtins.concatStringsSep " " binaries
