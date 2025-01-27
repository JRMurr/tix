let
  func = { other, ... }@arg: (arg.quz + (arg.foo + arg.bar) + (arg.bar + arg.baz));
in

func {
  quz = 0;
  foo = 1;
  bar = 3.14;
  baz = 5;
  other = "hello";
}
