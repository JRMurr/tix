{
  pkgs ? <nixpkgs>,
}:
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

  apply = fn: args: fn args;

  addTwo = apply add 2;

  addOne = add 1;

  two = addOne 1;

  three = add 1 2;

  /*
    Concatenate a list of strings.
    # Type
    ```
    concatStrings :: [string] -> string
    ```
  */
  concatStrings = builtins.concatStringsSep " ";

in

{
  inherit
    add
    addOne
    concatStrings
    two
    three
    apply
    addTwo
    ;
}
