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

  # Suppress the avalanche of deprecation/rename warnings that the NixOS and
  # Home Manager module systems emit during option tree evaluation. These
  # warnings are harmless (we only inspect the option *types*, not values) but
  # they clutter stderr and confuse users who see them during `nix build`.
  # We override lib.warn and friends with no-ops so builtins.trace is never
  # called for warning-level messages.
  quietLib = lib.extend (_self: _super: {
    warn = _msg: x: x;
    warnIf = _cond: _msg: x: x;
    warnIfNot = _cond: _msg: x: x;
    trivial = _super.trivial // {
      warn = _msg: x: x;
      warnIf = _cond: _msg: x: x;
      warnIfNot = _cond: _msg: x: x;
    };
  });

  # ============================================================================
  # NixOS option tree extraction (evaluated at Nix eval time)
  # ============================================================================

  # eval-config.nix defaults to builtins.currentSystem which isn't available
  # in pure flake evaluation, so we pass system explicitly from pkgs.
  nixosOptions = (import (pkgs.path + "/nixos/lib/eval-config.nix") {
    lib = quietLib;
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

  hmLib = import (hmSrc + "/modules/lib") { lib = quietLib; };
  extendedLib = quietLib.extend (_self: _super: { hm = hmLib; });

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
  # Pkgs attribute classification (evaluated at Nix eval time)
  # ============================================================================
  #
  # Recursively classifies nixpkgs attributes into derivation, attrset, or
  # function. Non-derivation attrsets with `recurseForDerivations = true` are
  # recursed into (same mechanism as `nix search` and Hydra). Broken or
  # unevaluable packages are skipped via tryEval.
  #
  # We import nixpkgs with allowAliases = false specifically for classification
  # to avoid the flood of "was renamed to" warnings that fire when traversing
  # deprecated alias attributes. The classification only cares about attribute
  # types (derivation/attrset/function), not alias behavior.
  classifyPkgs = import pkgs.path {
    inherit (pkgs.stdenv.hostPlatform) system;
    config = { allowAliases = false; };
  };

  classifySet = depth: attrset:
    builtins.listToAttrs (builtins.concatMap (name:
      let v = builtins.tryEval (builtins.getAttr name attrset);
      in if !v.success then []
      else let
        ty = builtins.typeOf v.value;
        isDrv = (builtins.tryEval ((v.value.type or null) == "derivation")).value or false;
        shouldRecurse = !isDrv && ty == "set" && depth > 0
          && ((builtins.tryEval (v.value.recurseForDerivations or false)).value or false);
        children = if shouldRecurse then classifySet (depth - 1) v.value else null;
      in [{
        inherit name;
        value = { type = ty; is_derivation = isDrv; }
          // (if children != null then { inherit children; } else {});
      }]
    ) (builtins.attrNames attrset));

  # Alias detection: for non-recursed attrsets where recurseForDerivations is
  # explicitly false (the dontRecurseIntoAttrs signature), find a recursed
  # sibling with identical attrNames. Only runs at the top level.
  namesOf = s: builtins.filter (n: n != "recurseForDerivations") (builtins.attrNames s);

  detectAliases = tree: attrset:
    let
      recursedNames = builtins.filter (name:
        (tree.${name} or {}) ? children
      ) (builtins.attrNames tree);
    in builtins.mapAttrs (name: entry:
      if entry ? children || entry ? alias_of
         || entry.is_derivation || entry.type != "set" then entry
      else let
        val = builtins.tryEval (builtins.getAttr name attrset);
        hasExplicitFalse = val.success
          && val.value ? recurseForDerivations
          && val.value.recurseForDerivations == false;
      in if !hasExplicitFalse then entry
      else let
        candNames = namesOf val.value;
        match = builtins.filter (rName:
          namesOf (builtins.getAttr rName attrset) == candNames
        ) recursedNames;
      in if match == [] then entry
         else entry // { alias_of = builtins.head match; }
    ) tree;

  pkgsClassificationJson = builtins.toJSON (detectAliases (classifySet 1 classifyPkgs) classifyPkgs);

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
