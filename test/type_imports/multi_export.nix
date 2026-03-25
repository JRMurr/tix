# Multiple type exports from a single file.
#
# Demonstrates exporting several type aliases, mixing pure parse-level types
# with typeof-based types.

/**
  type Name = string;
  type Version = string;
  type Meta = typeof meta;
*/
let
    meta = { license = "MIT"; homepage = "https://example.com"; };
    mkPackage = { name, version }:
        { inherit name version; inherit meta; };
in
    mkPackage { name = "tix"; version = "0.1.0"; }
