# The motivating example for Phase 4b: partial inference for typeof exports.
#
# This file declares a `scope` attrset and exports its type via `typeof scope`.
# Another file (package.nix) can import this type to annotate its parameter,
# even though this file also imports package.nix — partial inference breaks the
# potential cycle by only inferring `scope`'s SCC group (which doesn't depend
# on package.nix).

/**
  type Scope = typeof scope;
*/
let
    scope = {
        mkDerivation = args: args // { system = "x86_64-linux"; };
        lib = {
            id = x: x;
            const = x: _y: x;
        };
    };
    pkg = import ./package.nix scope;
in pkg
