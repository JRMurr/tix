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
    # Tests are run separately via rustTests (checks.tests) which has the
    # needed extra dependencies like nixfmt. Skip them here to avoid
    # duplicating test deps in the binary build.
    doCheck = false;

    # Ship support files for runtime stub generation. When tix runs outside
    # a dev shell, it finds these via its own store path.
    postInstall = ''
      mkdir -p $out/share/tix
      cp ${../stubs/lib.tix} $out/share/tix/lib.tix
      cp ${../nix/generate-stubs-runtime.nix} $out/share/tix/generate-stubs-runtime.nix
      cp ${../tools/extract-options.nix} $out/share/tix/extract-options.nix
    '';
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

  # Unit tests only. Integration tests (crates/*/tests/*.rs) are gated out
  # with `not kind(test)` because some of them need a real `nix` binary
  # available as a subprocess, which the nix build sandbox lacks. A
  # separate GitHub Actions step runs `kind(test)` via `nix develop`.
  rustTests = craneLib.cargoNextest (commonArgs // {
    inherit cargoArtifacts;
    nativeBuildInputs = [ pkgs.cargo-nextest pkgs.nixfmt ];
    cargoNextestExtraArgs = "-E 'not kind(test)' --failure-output immediate --success-output never";
  });

  # Property-based tests at an elevated case count: legacy proptest suites
  # under lang_check/src/pbt and hegel tests (`hegel_tests` modules) across
  # crates. PROPTEST_CASES is currently ignored by lang_check's explicit
  # configs (see SESSION.md); HEGEL_TEST_CASES overrides per-test settings.
  rustPbt = craneLib.cargoNextest (commonArgs // {
    inherit cargoArtifacts;
    nativeBuildInputs = [ pkgs.cargo-nextest ];
    pname = "tix-pbt";
    cargoNextestExtraArgs = "--workspace -E 'test(pbt) or test(hegel_tests)' --failure-output immediate --success-output never";
    PROPTEST_CASES = "10000";
    HEGEL_TEST_CASES = "10000";
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
