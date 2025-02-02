# let
#   foo = { }@arg: arg.bar;
# in
# # foo { bar = 1; } # type errors
# foo { } # does not type error

# let
#   add = a: b: a + b;
#   res = add 1 2;
# in
# res
# # {
# #   int = add 1 2;
# #   float = add 3.14 2;
# #   str = add "hi" ./test.nix;
# # }

# let
#   res = (a: b: a + b) 1 2;
# in
# res

# let
#   add = (a: b: a + b);
# in
# add 1 2

# let
#   id = (a: a);
# in
# id 1

# let
#   simple = {
#     foo = 100;
#   };
# in
# simple.foo

# let
#   display =
#     n:
#     if n == 0 then
#       ''zero''
#     else if n == 1 then
#       ''1''
#     else
#       ''BIG'';
# in
# display 3

let
  /**
    type: fib :: int -> int
  */
  fib =
    n:
    if n == 0 then
      0
    else if n == 1 then
      1
    else
      fib (n - 1) + fib (n - 2);
in
fib 3
