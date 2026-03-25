# Consumer of scope.nix's exported type.
#
# Uses import("./scope.nix").Scope to annotate its parameter, giving the
# type checker knowledge of the scope's shape without needing full inference
# of scope.nix (which would create a cycle since scope.nix imports this file).

/**
  type: args :: import("./scope.nix").Scope
*/
args:
    args.mkDerivation { name = "my-package"; src = ./.; }
