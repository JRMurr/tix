let
  even =
    x:
    if x == 0 then
      true
    else if x == 1 then
      false
    else
      even (x - 1);

in
even
