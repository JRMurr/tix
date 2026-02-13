let
    lib = import ./lib.nix;
in
{
    # id is polymorphic: used at int and string
    intResult = lib.id 42;
    strResult = lib.id "hello";
    doubled = lib.double 21;
}
