let
  /**
    this only works if i give it a type sig
    type: fix :: (a -> a) -> a
  */
  fix =
    f:
    let
      x = f x;
    in
    x;
in
{
  inherit fix;
  attr = fix (self: {
    foo = "foo";
    bar = "bar";
    foobar = self.foo + self.bar;
  });

  test = (
    let
      self = {
        foo = "foo";
        bar = "bar";
        foobar = self.foo + self.bar;
      };
    in
    self
  );
}
