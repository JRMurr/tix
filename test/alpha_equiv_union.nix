let
  get_fun = x: if x == "sub" then (y: y - 1) else (y: y + 1);
in
get_fun
