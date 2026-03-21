# ==============================================================================
# Runtime Stubs Generation (standalone, parameterized)
# ==============================================================================
#
# Called by `tix` at runtime to generate stubs from a given nixpkgs (and
# optionally home-manager) store path. Also used by the flake's stubs.nix
# as the shared implementation.
#
# All arguments are store paths. `home-manager-path` is optional (null skips
# HM stub generation). `extract-options-nix` is the path to the option tree
# extraction helper.

{
  nixpkgs-path,
  tix-path,
  home-manager-path ? null,
  extract-options-nix ? (tix-path + "/share/tix/extract-options.nix"),
  lib-tix-path ? (tix-path + "/share/tix/lib.tix"),
}:

let
  pkgs = import nixpkgs-path { };
  lib = pkgs.lib;

  # Suppress deprecation/rename warnings from the NixOS and Home Manager
  # module systems. We only inspect option *types*, not values.
  quietLib = lib.extend (
    _self: _super: {
      warn = _msg: x: x;
      warnIf =
        _cond: _msg: x:
        x;
      warnIfNot =
        _cond: _msg: x:
        x;
      trivial = _super.trivial // {
        warn = _msg: x: x;
        warnIf =
          _cond: _msg: x:
          x;
        warnIfNot =
          _cond: _msg: x:
          x;
      };
    }
  );

  # ============================================================================
  # NixOS option tree extraction
  # ============================================================================

  nixosOptions =
    (import (nixpkgs-path + "/nixos/lib/eval-config.nix") {
      lib = quietLib;
      system = pkgs.stdenv.hostPlatform.system;
      modules = [ { _module.check = false; } ];
    }).options;

  nixosOptionsJson = builtins.toJSON (
    import extract-options-nix {
      options = nixosOptions;
      maxDepth = 8;
    }
  );

  # ============================================================================
  # Home Manager option tree extraction (only if home-manager-path is provided)
  # ============================================================================

  hmOptionsJson =
    if home-manager-path == null then
      null
    else
      let
        hmSrc = home-manager-path;
        hmLib = import (hmSrc + "/modules/lib") { lib = quietLib; };
        extendedLib = quietLib.extend (_self: _super: { hm = hmLib; });
        hmModuleList = import (hmSrc + "/modules/modules.nix") {
          inherit pkgs;
          lib = extendedLib;
          check = false;
        };
        hmEval = extendedLib.evalModules {
          modules = hmModuleList ++ [
            {
              _module.check = false;
              _module.args = {
                inherit pkgs;
                osConfig = { };
              };
            }
          ];
        };
      in
      builtins.toJSON (
        import extract-options-nix {
          options = hmEval.options;
          maxDepth = 8;
        }
      );

  # ============================================================================
  # Pkgs attribute classification
  # ============================================================================

  classifyPkgs = import nixpkgs-path {
    inherit (pkgs.stdenv.hostPlatform) system;
    config = {
      allowAliases = false;
    };
  };

  classifySet =
    depth: attrset:
    builtins.listToAttrs (
      builtins.concatMap (
        name:
        let
          v = builtins.tryEval (builtins.getAttr name attrset);
        in
        if !v.success then
          [ ]
        else
          let
            ty = builtins.typeOf v.value;
            isDrv = (builtins.tryEval ((v.value.type or null) == "derivation")).value or false;
            shouldRecurse =
              !isDrv
              && ty == "set"
              && depth > 0
              && ((builtins.tryEval (v.value.recurseForDerivations or false)).value or false);
            children = if shouldRecurse then classifySet (depth - 1) v.value else null;
            hasFunctor =
              !isDrv && ty == "set" && (builtins.tryEval (v.value ? __functor)).value or false;
            funcArgs =
              if ty == "lambda" then
                (builtins.tryEval (builtins.functionArgs v.value)).value or null
              else
                null;
          in
          [
            {
              inherit name;
              value =
                {
                  type = ty;
                  is_derivation = isDrv;
                }
                // (if hasFunctor then { has_functor = true; } else { })
                // (if funcArgs != null then { function_args = funcArgs; } else { })
                // (if children != null then { inherit children; } else { });
            }
          ]
      ) (builtins.attrNames attrset)
    );

  namesOf = s: builtins.filter (n: n != "recurseForDerivations") (builtins.attrNames s);

  detectAliases =
    tree: attrset:
    let
      recursedNames = builtins.filter (name: (tree.${name} or { }) ? children) (
        builtins.attrNames tree
      );
    in
    builtins.mapAttrs (
      name: entry:
      if entry ? children || entry ? alias_of || entry.is_derivation || entry.type != "set" then
        entry
      else
        let
          val = builtins.tryEval (builtins.getAttr name attrset);
          hasExplicitFalse =
            val.success
            && val.value ? recurseForDerivations
            && val.value.recurseForDerivations == false;
        in
        if !hasExplicitFalse then
          entry
        else
          let
            candNames = namesOf val.value;
            match = builtins.filter (
              rName: namesOf (builtins.getAttr rName attrset) == candNames
            ) recursedNames;
          in
          if match == [ ] then entry else entry // { alias_of = builtins.head match; }
    ) tree;

  pkgsClassificationJson = builtins.toJSON (detectAliases (classifySet 1 classifyPkgs) classifyPkgs);

  # ============================================================================
  # Convert JSON -> .tix using tix --from-json
  # ============================================================================

  nixosJsonFile = pkgs.writeText "nixos-options.json" nixosOptionsJson;
  pkgsJsonFile = pkgs.writeText "pkgs-classification.json" pkgsClassificationJson;
  hmJsonFile =
    if hmOptionsJson != null then pkgs.writeText "hm-options.json" hmOptionsJson else null;

in
pkgs.runCommand "tix-stubs"
  {
    nativeBuildInputs = [ tix-path ];
  }
  ''
    mkdir -p $out
    tix gen-stubs nixos --from-json ${nixosJsonFile} --descriptions -o $out/nixos.tix
    ${lib.optionalString (hmJsonFile != null) "tix gen-stubs home-manager --from-json ${hmJsonFile} --descriptions -o $out/home-manager.tix"}
    tix gen-stubs pkgs --from-json ${pkgsJsonFile} -o $out/pkgs.tix
    cp ${lib-tix-path} $out/lib.tix
  ''
