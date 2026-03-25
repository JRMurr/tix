# Demonstrates composing type operators with cross-file type imports.
#
# Uses Param, Return, and field access on imported types.

/**
  type Builder = { name: string, src: path, ... } -> { name: string, out: path };
*/
let
    builder = { name, src, ... }: { inherit name; out = src; };

    # Param extracts the parameter type of a local function
    /** type: input :: Param(typeof builder) */
    input = { name = "hello"; src = ./.; };

    # Return extracts the return type
    /** type: output :: Return(typeof builder) */
    output = builder input;
in
{
    inherit input output;
    out_name = output.name;
}
