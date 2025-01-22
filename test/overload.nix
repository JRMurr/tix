{
  # pbt would be great for this....
  neg_int = -(1 * 5);
  neg_float = -(3.14);

  int_float_add = 1 + 3.14;
  float_int_add = 3.14 + 1;
  int_add = 1 + 3;
  float_add = 3.14 + 5.3;

  int_mul = 4 * 5;
  float_int_mul = 3.14 * 5;

  int_div = 4 / 3;
  float_int_div = 5.0 / 2;

  string_add = "hello" + "world";
  path_add = ./overload.nix + ./overload.nix;
  string_path_add = "hello" + ./overload.nix;
  path_string_add = ./overload.nix + "hello";

  # sad stuff
  # sad = -"12";
}
