# Imports a type declaration from another file's doc comments.
#
# Uses import("./config.nix").Config to annotate a binding, giving the type
# checker the expected shape without needing to infer config.nix.

let
  /**
    type: cfg :: import("./config.nix").Config
  */
  cfg = {
    name = "myapp";
    debug = true;
    port = 3000;
  };
in
import ./config.nix cfg
