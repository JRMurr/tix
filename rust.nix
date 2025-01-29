{ pkgs, gitignore }:

let
  rustVersion = (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml); # rust-bin.stable.latest.default
  rustPlatform = pkgs.makeRustPlatform {
    cargo = rustVersion;
    rustc = rustVersion;
  };
  name = "tix";
  version = "0.1.0";
  rustBin = rustPlatform.buildRustPackage {
    pname = name;
    version = version;
    src = gitignore.lib.gitignoreSource ./.;
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
