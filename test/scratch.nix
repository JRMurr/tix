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

[
  (
    (
      param:
      let
        tmp = ((un_used_param: (0.0749) * (-0.3111)));
      in
      if
        param == (
          let
            _pbt_C = ((0) - (-55));
          in
          _pbt_C
        )
      then
        tmp
      else
        tmp
    )
  )
]
