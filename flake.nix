{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
      ...
    }:
    (
      flake-utils.lib.eachDefaultSystem (
        system:
        let

          overlays = [ (import rust-overlay) ];
          /**
            type: pkgs :: Pkgs
          */
          pkgs = import nixpkgs { inherit system overlays; };
          rustAttrs = import ./rust.nix { inherit pkgs; };
          tix-lsp-dev = import ./lsp-dev.nix { inherit pkgs; };
        in
        {
          formatter = pkgs.nixfmt;

          devShells = {
            default = pkgs.mkShell {
              buildInputs = [
                rustAttrs.rust-shell
                (pkgs.cargo-tarpaulin.override ({ rustPlatform = rustAttrs.rustPlatform; }))
                tix-lsp-dev

                # common
                pkgs.just
              ];
            };
          };
          packages = {
            default = rustAttrs.binary;
            rust-bin = rustAttrs.binary;
            # rust-docker = rustAttrs.docker;
          };

        }
      )
      // {

        overlays = {
          # compose with rust-overlay so the nix build wokred
          # TODO: see if we can do the build without the rust overlay
          default = nixpkgs.lib.composeExtensions self.overlays.rust-overlay self.overlays.tix;

          rust-overlay = (import rust-overlay);

          tix = import ./overlay.nix;
        };
      }
    );
}
