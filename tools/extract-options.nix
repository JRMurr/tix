# ==============================================================================
# NixOS Option Tree → JSON Extractor
# ==============================================================================
#
# Walks the NixOS option tree and produces a JSON-serializable structure that
# tix-cli can consume to generate `.tix` type stubs.
#
# Usage (standalone):
#   nix eval --json --expr 'import ./extract-options.nix { options = (import <nixpkgs/nixos> {}).options; }'
#
# Called by tix-cli gen-stubs nixos — not intended for direct use.

{ options, maxDepth ? 8 }:

let
  # ============================================================================
  # Type Extraction
  # ============================================================================
  #
  # NixOS option types carry a `name` field that identifies the type constructor.
  # We pattern-match on this name to produce a JSON-friendly representation.
  # Some types wrap inner types (listOf, attrsOf, nullOr, etc.) that we recurse
  # into. Unknown types fall through to `{ type = "anything"; }`.

  extractType = depth: optType:
    let
      name = optType.name or "";
    in
    if depth <= 0 then { type = "anything"; }

    # --- Primitive types ---
    else if name == "str" || name == "separatedString" || name == "lines"
            || name == "commas" || name == "envVar" || name == "nonEmptyStr" then
      { type = "primitive"; value = "string"; }

    else if name == "int" || name == "ints.signed" || name == "ints.unsigned"
            || name == "ints.positive" || name == "ints.s8" || name == "ints.s16"
            || name == "ints.s32" || name == "ints.u8" || name == "ints.u16"
            || name == "ints.u32" || name == "port" then
      { type = "primitive"; value = "int"; }

    else if name == "bool" then
      { type = "primitive"; value = "bool"; }

    else if name == "float" then
      { type = "primitive"; value = "float"; }

    else if name == "path" then
      { type = "primitive"; value = "path"; }

    # --- Package type (a derivation) ---
    else if name == "package" then
      { type = "package"; }

    # --- Compound types ---
    else if name == "listOf" then
      let inner = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.elemType);
      in { type = "list"; elem = if inner.success then inner.value else { type = "anything"; }; }

    else if name == "attrsOf" || name == "lazyAttrsOf" then
      let inner = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.elemType);
      in { type = "attrsOf"; elem = if inner.success then inner.value else { type = "anything"; }; }

    else if name == "nullOr" then
      let inner = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.elemType);
      in { type = "nullOr"; elem = if inner.success then inner.value else { type = "anything"; }; }

    else if name == "either" || name == "oneOf" then
      let
        left = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.left);
        right = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.right);
      in { type = "union"; members = builtins.filter (x: x != null) [
        (if left.success then left.value else null)
        (if right.success then right.value else null)
      ]; }

    else if name == "enum" then
      { type = "enum"; }

    else if name == "submodule" then
      let
        # Submodule options are accessible via the `getSubOptions []` call.
        subOpts = builtins.tryEval (optType.getSubOptions []);
      in
      if subOpts.success then
        { type = "submodule"; options = walkOptions (depth - 1) subOpts.value; }
      else
        { type = "anything"; }

    else if name == "functionTo" then
      let inner = builtins.tryEval (extractType (depth - 1) optType.nestedTypes.elemType);
      in { type = "function"; result = if inner.success then inner.value else { type = "anything"; }; }

    # --- Wrapper types (unwrap to inner type) ---
    else if name == "uniq" || name == "unique" then
      let inner = builtins.tryEval (extractType depth optType.nestedTypes.elemType);
      in if inner.success then inner.value else { type = "anything"; }

    else if name == "coercedTo" then
      # coercedTo wraps a final type — extract it
      let inner = builtins.tryEval (extractType depth optType.nestedTypes.finalType);
      in if inner.success then inner.value else { type = "anything"; }

    else if name == "anything" || name == "raw" || name == "unspecified" then
      { type = "anything"; }

    # --- Fallback ---
    else
      { type = "anything"; };


  # ============================================================================
  # Option Tree Walking
  # ============================================================================
  #
  # NixOS options form a tree where leaves are actual options (they have
  # `_type = "option"`) and branches are attribute sets grouping related options.
  # Internal attrs like `_module` are filtered out.

  isOption = v:
    let tried = builtins.tryEval (v._type or "");
    in tried.success && tried.value == "option";

  walkOptions = depth: opts:
    if depth <= 0 then {}
    else
      let
        names = builtins.tryEval (builtins.attrNames opts);
        safeNames = if names.success then
          builtins.filter (n: n != "_module" && n != "_freeformOptions") names.value
        else [];
      in
      builtins.listToAttrs (builtins.concatMap (name:
        let
          val = builtins.tryEval (builtins.getAttr name opts);
        in
        if !val.success then []
        else
          let v = val.value; in
          if isOption v then
            let
              typeInfo = builtins.tryEval (extractType (depth - 1) v.type);
              # Extract the option description. Handles three cases:
              #   1. Plain string: `description = "some text";`
              #   2. mdDoc attrset: `description = lib.mdDoc "some text";` → `{ _type = "mdDoc"; text = "..."; }`
              #   3. Missing/unevaluable: fall back to null
              rawDesc = builtins.tryEval (v.description or null);
              desc =
                if !rawDesc.success then null
                else if rawDesc.value == null then null
                else if builtins.isString rawDesc.value then rawDesc.value
                else if builtins.isAttrs rawDesc.value && (rawDesc.value.text or null) != null
                  then rawDesc.value.text
                else null;
            in [{
              inherit name;
              value = {
                _isOption = true;
                typeInfo = if typeInfo.success then typeInfo.value else { type = "anything"; };
              } // (if desc != null then { description = desc; } else {});
            }]
          else if builtins.isAttrs v then
            [{
              inherit name;
              value = {
                _isOption = false;
                children = walkOptions (depth - 1) v;
              };
            }]
          else []
      ) safeNames);

in
  walkOptions maxDepth options
