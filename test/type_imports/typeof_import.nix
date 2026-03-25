# Uses typeof import("path") to reference the inferred root type of another file.
#
# This requires full inference of the target file (unlike import("path").TypeName
# which only reads doc comments or does partial inference).

let
    /**
      type: data :: typeof import("./config.nix")
    */
    data = import ./config.nix { name = "test"; };
in
    data.greeting
