{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
}:

let
  lib = pkgs.lib;
  rustVersion = (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml); # rust-bin.stable.latest.default
  rustPlatform = pkgs.makeRustPlatform {
    cargo = rustVersion;
    rustc = rustVersion;
  };
  name = "tix";
  version = "0.1.0";

  fs = lib.fileset;
  baseSrc = fs.unions [ ./crates ./Cargo.toml ./Cargo.lock ];

  src = fs.toSource {
    root = ./.;
    fileset = baseSrc;
  };
  # filterMarkdownFiles = fs.fileFilter (file: lib.strings.hasSuffix ".md" file.name) ./.;
  # removedMarkedDown = fs.difference baseSrc filterMarkdownFiles;

  rustBin = rustPlatform.buildRustPackage {
    inherit src;
    pname = name;
    version = version;
    
    cargoLock.lockFile = ./Cargo.lock;
    nativeBuildInputs = [ ];
  };
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
