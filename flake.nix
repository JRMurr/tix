{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
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
          rustAttrs = import ./nix/rust.nix { inherit pkgs crane; };
          tix-lsp-dev = import ./nix/lsp-local.nix { inherit pkgs; name = "tix-lsp-dev"; };
          tix-lsp-release = import ./nix/lsp-local.nix { inherit pkgs; profile = "release"; };
          tix-code = import ./nix/vscode.nix {
            inherit pkgs;
            serverPath = "${tix-with-stubs}/bin/tix";
            serverArgs = [ "lsp" ];
          };
          tix-code-dev = import ./nix/vscode.nix {
            inherit pkgs;
            serverPath = "${tix-lsp-dev}/bin/tix-lsp-dev";
            name = "tix-code-dev";
          };
          tix-code-release = import ./nix/vscode.nix {
            inherit pkgs;
            serverPath = "${tix-lsp-release}/bin/tix-lsp-release";
            name = "tix-code-release";
          };

          tix-stubs = import ./nix/stubs.nix {
            inherit pkgs;
            home-manager = home-manager;
            tix = rustAttrs.binary;
          };

          scripts = import ./nix/scripts.nix {
            inherit pkgs;
            nixpkgs-src = nixpkgs.outPath;
          };

          # Wraps the tix binary so that @nixos and @home-manager context
          # references in tix.toml resolve to the fully-typed generated stubs
          # instead of the minimal compiled-in ones.
          tix-with-stubs = pkgs.symlinkJoin {
            name = "tix-with-stubs";
            paths = [ rustAttrs.binary ];
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/tix \
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
                pkgs.cargo-nextest
                tix-lsp-dev
                scripts.tixc
                scripts.nixpkgs-test

                # common
                pkgs.just
                pkgs.mdbook
                pkgs.mdbook-mermaid
              ];
            };
          };
          packages = {
            default = rustAttrs.binary;
            rust-bin = rustAttrs.binary;
            stubs = tix-stubs;
            with-stubs = tix-with-stubs;
            inherit tix-code tix-code-dev tix-code-release;
            inherit (scripts) tixc nixpkgs-test;
            docs = pkgs.stdenv.mkDerivation {
              name = "tix-docs";
              src = ./docs;
              nativeBuildInputs = [ pkgs.mdbook pkgs.mdbook-mermaid ];
              buildPhase = ''
                mdbook-mermaid install .
                mdbook build -d $out
              '';
              dontInstall = true;
            };
            # rust-docker = rustAttrs.docker;
          };

          checks = rustAttrs.checks // {
            # Verify the with-stubs wrapper (TIX_BUILTIN_STUBS baked in via
            # makeWrapper) can type-check files that use @nixos and
            # @home-manager contexts end-to-end.
            with-stubs =
              pkgs.runCommand "tix-check-with-stubs"
                {
                  nativeBuildInputs = [ tix-with-stubs ];
                }
                ''
                  cp -r ${./test} test_files
                  chmod -R u+w test_files

                  # Test @nixos context: test/tix.toml maps nixos_module.nix to @nixos
                  tix test_files/nixos_module.nix --config test_files/tix.toml

                  # Test @home-manager context: nixos_fixture/tix.toml maps home/*.nix to @home-manager
                  tix test_files/nixos_fixture/home/shell.nix \
                    --config test_files/nixos_fixture/tix.toml

                  touch $out
                '';

            # Verify the runtime stub generation pipeline:
            #   extract-options.nix produces pos fields (declarationPositions)
            #   → tix gen-stubs emits @source annotations
            #   → generated .tix files parse successfully
            stub-generation =
              let
                stubs = tix-stubs;
              in
              pkgs.runCommand "tix-check-stub-generation"
                {
                  nativeBuildInputs = [ tix-with-stubs pkgs.jq ];
                }
                ''
                  echo "=== Checking generated stubs exist ==="
                  for f in nixos.tix home-manager.tix pkgs.tix lib.tix; do
                    test -f ${stubs}/$f || { echo "FAIL: $f missing"; exit 1; }
                    echo "  $f exists ($(wc -l < ${stubs}/$f) lines)"
                  done

                  echo "=== Checking @source annotations ==="
                  for f in nixos.tix home-manager.tix pkgs.tix lib.tix; do
                    count=$(grep -c '@source' ${stubs}/$f || true)
                    echo "  $f: $count @source annotations"
                  done

                  # NixOS options should have many @source annotations from
                  # declarationPositions. Fail if fewer than 1000 — that would
                  # indicate the extraction regressed.
                  nixos_count=$(grep -c '@source' ${stubs}/nixos.tix || true)
                  if [ "$nixos_count" -lt 1000 ]; then
                    echo "FAIL: nixos.tix has only $nixos_count @source annotations (expected >= 1000)"
                    exit 1
                  fi

                  # pkgs should have @source from unsafeGetAttrPos + meta.position fallback
                  pkgs_count=$(grep -c '@source' ${stubs}/pkgs.tix || true)
                  if [ "$pkgs_count" -lt 1000 ]; then
                    echo "FAIL: pkgs.tix has only $pkgs_count @source annotations (expected >= 1000)"
                    exit 1
                  fi

                  # lib.tix @source comes from noogle data
                  lib_count=$(grep -c '@source' ${stubs}/lib.tix || true)
                  if [ "$lib_count" -lt 100 ]; then
                    echo "FAIL: lib.tix has only $lib_count @source annotations (expected >= 100)"
                    exit 1
                  fi

                  echo "=== Checking generated stubs parse ==="
                  for f in nixos.tix pkgs.tix lib.tix; do
                    tix --no-default-stubs --stubs ${stubs}/$f /dev/null \
                      || { echo "FAIL: $f failed to parse"; exit 1; }
                    echo "  $f parses OK"
                  done

                  echo "=== All stub generation checks passed ==="
                  touch $out
                '';
          };

        }
      )
      // {

        # Exposed as a plain string attribute so scripts can resolve the
        # pinned nixpkgs source via `nix eval --raw .#nixpkgs-src`.
        # Kept outside `packages` because it's not a derivation and
        # `nix flake check` rejects non-derivation package outputs.
        nixpkgs-src = nixpkgs.outPath;

        overlays = {
          # compose with rust-overlay so the nix build wokred
          # TODO: see if we can do the build without the rust overlay
          default = nixpkgs.lib.composeExtensions self.overlays.rust-overlay self.overlays.tix;

          rust-overlay = (import rust-overlay);

          tix = import ./nix/overlay.nix { inherit crane; };
        };
      }
    );
}
