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

# (
#   param:
#   let
#     tmp = ("test");
#   in
#   if param == 1 then tmp else tmp
# )

(
  param:
  let
    tmp = (({ _pbt_a = ((un_used_param: null)); }));
  in
  if param == (un_used_param: null) then tmp else tmp
)
