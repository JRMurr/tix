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

(
  param:
  let
    tmp = (
      (
        ({
          _pbt_0EIXC9G_u = (null);
          _pbt_u7_n_u4_W2 = ((-0.2382) * ((0.1526) * ((1538430809) - ((999973906) / (-245347219)))));
          _pbt__nx__X_T = ((((-775235504) * (976876505)) + (170057216)) - (-467874792));
          _pbt_4_w____C9W = ((((true) && (true)) || (false)) || ((false) || (true)));
          _pbt__5_8_ = (({ }));
        })._pbt__5_8_
      )
    );
  in
  if
    param == (({ _pbt_a = ([ ((({ _pbt_1 = ((728909406) + (291607382)); })._pbt_1)) ]); })._pbt_a)
  then
    tmp
  else
    tmp
)
