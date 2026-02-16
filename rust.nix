{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
  crane,
}:

let
  lib = pkgs.lib;
  rustVersion = (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml);
  rustPlatform = pkgs.makeRustPlatform {
    cargo = rustVersion;
    rustc = rustVersion;
  };

  craneLib = (crane.mkLib pkgs).overrideToolchain rustVersion;

  fs = lib.fileset;
  src = fs.toSource {
    root = ./.;
    fileset = fs.unions [
      ./crates
      ./Cargo.toml
      ./Cargo.lock
      ./stubs
      ./tools
    ];
  };

  commonArgs = {
    inherit src;
    pname = "tix";
    version = "0.1.0";
  };

  # Phase 1: Build only third-party dependencies (cached separately).
  # Rebuilds only when Cargo.toml or Cargo.lock changes.
  cargoArtifacts = craneLib.buildDepsOnly commonArgs;

  # Phase 2: Build workspace crates, reusing pre-built deps.
  rustBin = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts;
  });
in
{
  inherit rustPlatform;
  rust-shell = (
    rustVersion.override {
      extensions = [
        "rust-src"
        "rust-analyzer"
      ];
    }
  );
  binary = rustBin;
}
