let
    /**
        type: lib :: Lib
    */
    lib = import ./lib.nix;

    /**
        type: pkgs :: Pkgs
    */
    pkgs = import ./pkgs.nix;

    greeting = lib.strings.concatStringsSep ", " ["hello" "world"];
    identity = lib.id 42;
    names = lib.lists.map (x: x.name) [{ name = "alice"; } { name = "bob"; }];

    drv = pkgs.stdenv.mkDerivation { name = "my-package"; src = ./.; };
    src = pkgs.fetchFromGitHub {
        owner = "NixOS";
        repo = "nixpkgs";
        rev = "abc123";
        sha256 = "000";
    };
in
{
    inherit greeting identity names drv src;
}
