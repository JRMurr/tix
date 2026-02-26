{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
  crane,
}:

let
  lib = pkgs.lib;
  rustVersion = (pkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml);
  rustPlatform = pkgs.makeRustPlatform {
    cargo = rustVersion;
    rustc = rustVersion;
  };

  craneLib = (crane.mkLib pkgs).overrideToolchain rustVersion;

  fs = lib.fileset;
  src = fs.toSource {
    root = ./..;
    fileset = fs.unions [
      ../crates
      ../Cargo.toml
      ../Cargo.lock
      ../stubs
      ../tools
      ../test
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

  # ==============================================================================
  # CI Checks — all reuse the same cargoArtifacts so deps are compiled once
  # ==============================================================================

  rustFmt = craneLib.cargoFmt {
    inherit src;
    pname = "tix";
    version = "0.1.0";
    # cargoFmt doesn't need compiled artifacts, just the source
  };

  rustClippy = craneLib.cargoClippy (commonArgs // {
    inherit cargoArtifacts;
    cargoClippyExtraArgs = "-- -D warnings";
  });

  rustTests = craneLib.cargoTest (commonArgs // {
    inherit cargoArtifacts;
  });

  # PBT runs two groups with different case counts (mirroring scripts/pbt.sh).
  # Lightweight tests get 10k cases, stub composition tests get 2k.
  rustPbt = craneLib.cargoTest (commonArgs // {
    inherit cargoArtifacts;
    pname = "tix-pbt";
    cargoTestExtraArgs = "--package lang_check --lib -- pbt";
    PROPTEST_CASES = "10000";
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
  checks = {
    fmt = rustFmt;
    clippy = rustClippy;
    tests = rustTests;
    pbt = rustPbt;
  };
}
