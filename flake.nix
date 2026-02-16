{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
    home-manager = {
      url = "github:nix-community/home-manager";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
      crane,
      home-manager,
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
          rustAttrs = import ./rust.nix { inherit pkgs crane; };
          tix-lsp-dev = import ./lsp-dev.nix { inherit pkgs; };

          tix-stubs = import ./stubs.nix {
            inherit pkgs;
            home-manager = home-manager;
            tix-cli = rustAttrs.binary;
          };

          # Wraps the tix-cli binary so that @nixos and @home-manager context
          # references in tix.toml resolve to the fully-typed generated stubs
          # instead of the minimal compiled-in ones.
          tix-with-stubs = pkgs.symlinkJoin {
            name = "tix-with-stubs";
            paths = [ rustAttrs.binary ];
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/tix-cli \
                --set TIX_BUILTIN_STUBS "${tix-stubs}"
              wrapProgram $out/bin/tix-lsp \
                --set TIX_BUILTIN_STUBS "${tix-stubs}"
            '';
          };
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
            stubs = tix-stubs;
            with-stubs = tix-with-stubs;
            # rust-docker = rustAttrs.docker;
          };

          checks = {
            # Verify the with-stubs wrapper (TIX_BUILTIN_STUBS baked in via
            # makeWrapper) can type-check files that use @nixos and
            # @home-manager contexts end-to-end.
            with-stubs = pkgs.runCommand "tix-check-with-stubs" {
              nativeBuildInputs = [ tix-with-stubs ];
            } ''
              cp -r ${./test} test_files
              chmod -R u+w test_files

              # Test @nixos context: test/tix.toml maps nixos_module.nix to @nixos
              tix-cli test_files/nixos_module.nix --config test_files/tix.toml

              # Test @home-manager context: nixos_fixture/tix.toml maps home/*.nix to @home-manager
              tix-cli test_files/nixos_fixture/home/shell.nix \
                --config test_files/nixos_fixture/tix.toml

              touch $out
            '';
          };

        }
      )
      // {

        overlays = {
          # compose with rust-overlay so the nix build wokred
          # TODO: see if we can do the build without the rust overlay
          default = nixpkgs.lib.composeExtensions self.overlays.rust-overlay self.overlays.tix;

          rust-overlay = (import rust-overlay);

          tix = import ./overlay.nix { inherit crane; };
        };
      }
    );
}
