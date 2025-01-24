let
  merged =
    {
      a = 1;
      b = 2;
    }
    // {
      a = "hi";
      c = ./merge.nix;
    };
in
merged
