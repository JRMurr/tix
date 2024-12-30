{
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

  addOne = (a: b: a + b) 1;

  attr = {
    f1 = 1;
    f2 = 2;
  };

}
