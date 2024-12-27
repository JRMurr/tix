{ pkgs }:
let
  /**
      This function adds two numbers

      # Example

      ```nix
      add 4 5
      =>
      9
      ```

      # Type

      ```
      add :: Number -> Number -> Number
      ```

      # Arguments

      a
      : The first number

      b
      : The second number
  */
  add = a: b: a + b;

  addOne = add 1;

  two = addOne 1;

  /*
    Concatenate a list of strings.
    # Type
    ```
    concatStrings :: [string] -> string
    ```
  */
  concatStrings = builtins.concatStringsSep "";
in
{
  inherit
    add
    addOne
    concatStrings
    two
    ;
}
