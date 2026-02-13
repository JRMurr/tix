- need to have cases like `{}@arg: arg.baz` type error at func def


# ML sub

This might be generalizing a little too hard at the moment. `cargo run test/basic.nix` gives a very weird type for apply that should just be a simple generic.
Its also not correctly inferring that `three` is an Int.
No sure if this is ml sub or the claude migration.