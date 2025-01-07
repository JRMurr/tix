let
  # these are builtins...
  # true = 1;
  # false = 0;

  even =
    x:
    if x == 0 then
      1 # true
    else if x == 1 then
      0 # false
    else
      odd (x - 1);

  odd =
    x:
    if x == 0 then
      0 # false
    else if x == 1 then
      1 # true
    else
      even (x - 1);
in
odd 17
