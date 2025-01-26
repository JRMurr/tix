let
  even =
    x:
    if x == 0 then
      true
    else if x == 1 then
      false
    else
      odd (x - 1);

  odd =
    x:
    if x == 0 then
      false
    else if x == 1 then
      true
    else
      even (x - 1);
in
odd 17
