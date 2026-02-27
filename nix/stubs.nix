# ==============================================================================
# Generated Stubs Derivation
# ==============================================================================
#
# Evaluates NixOS and Home Manager option trees and classifies nixpkgs
# top-level attributes in pure Nix, then uses tix-cli --from-json to convert
# the JSON into .tix stub files. This avoids needing `nix eval --impure`
# inside the build sandbox.
#
# The option tree evaluation happens at Nix eval time (via builtins.toJSON),
# so it adds to the evaluation phase but keeps the build phase pure and simple.

{
  pkgs,
  home-manager,
  tix-cli,
}:

let
  lib = pkgs.lib;

  # ============================================================================
  # NixOS option tree extraction (evaluated at Nix eval time)
  # ============================================================================

  # eval-config.nix defaults to builtins.currentSystem which isn't available
  # in pure flake evaluation, so we pass system explicitly from pkgs.
  nixosOptions = (import (pkgs.path + "/nixos/lib/eval-config.nix") {
    system = pkgs.stdenv.hostPlatform.system;
    modules = [{ _module.check = false; }];
  }).options;

  nixosOptionsJson = builtins.toJSON (
    import ../tools/extract-options.nix {
      options = nixosOptions;
      maxDepth = 8;
    }
  );

  # ============================================================================
  # Home Manager option tree extraction (evaluated at Nix eval time)
  # ============================================================================

  hmSrc = home-manager;

  hmLib = import (hmSrc + "/modules/lib") { inherit (pkgs) lib; };
  extendedLib = pkgs.lib.extend (_self: _super: { hm = hmLib; });

  hmModuleList = import (hmSrc + "/modules/modules.nix") {
    inherit pkgs;
    lib = extendedLib;
    check = false;
  };

  hmEval = extendedLib.evalModules {
    modules = hmModuleList ++ [{
      _module.check = false;
      _module.args = {
        inherit pkgs;
        osConfig = {};
      };
    }];
  };

  hmOptionsJson = builtins.toJSON (
    import ../tools/extract-options.nix {
      options = hmEval.options;
      maxDepth = 8;
    }
  );

  # ============================================================================
  # Pkgs top-level attribute classification (evaluated at Nix eval time)
  # ============================================================================
  #
  # Classifies every top-level nixpkgs attribute into derivation, attrset, or
  # function. Broken/unevaluable packages are skipped via tryEval.

  classifyPkg = name: let
    v = builtins.tryEval (builtins.getAttr name pkgs);
  in if !v.success then null
     else {
       inherit name;
       type = builtins.typeOf v.value;
       is_derivation = (builtins.tryEval ((v.value.type or null) == "derivation")).value or false;
     };

  pkgsClassification = builtins.filter (x: x != null)
    (builtins.map classifyPkg (builtins.attrNames pkgs));

  pkgsClassificationJson = builtins.toJSON pkgsClassification;

  # ============================================================================
  # Convert JSON → .tix using tix-cli --from-json
  # ============================================================================

  nixosJsonFile = pkgs.writeText "nixos-options.json" nixosOptionsJson;
  hmJsonFile = pkgs.writeText "hm-options.json" hmOptionsJson;
  pkgsJsonFile = pkgs.writeText "pkgs-classification.json" pkgsClassificationJson;

in pkgs.runCommand "tix-stubs" {
  nativeBuildInputs = [ tix-cli ];
} ''
  mkdir -p $out
  tix-cli gen-stubs nixos --from-json ${nixosJsonFile} --descriptions -o $out/nixos.tix
  tix-cli gen-stubs home-manager --from-json ${hmJsonFile} --descriptions -o $out/home-manager.tix
  tix-cli gen-stubs pkgs --from-json ${pkgsJsonFile} -o $out/pkgs.tix
''
