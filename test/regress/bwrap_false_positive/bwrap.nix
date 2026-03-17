{
  /**
    type: pkgs :: Pkgs
  */
  pkgs,
}:
let

  lib = pkgs.lib;

  network = import ./network.nix { inherit pkgs; };

  nix_proxy = { nix_proxy = null; }.nix_proxy;

  bubblewrap_helper =
    {
      args,
      name,
      script,
      nixProxy ? null,
      pasta ? null,
      paths ? null,
      proxy ? null,
    }:
    let
      inner_script = pkgs.writeShellScript name script;

      proxy_enabled = proxy != null;
      proxy_allow_list =
        if proxy != null then (proxy.allowlist or network.defaultProxyAllowlist) else [ ];

      nix_proxy_enabled = nixProxy != null;
      nix_proxy_allowed_system_features =
        if nix_proxy_enabled then (nixProxy.allowedSystemFeatures or "none") else "none";
      nix_proxy_allowed_setting_overrides =
        if nix_proxy_enabled then (nixProxy.allowedSettingOverrides or "none") else "none";
      nix_proxy_allowed_build_modes =
        if nix_proxy_enabled then (nixProxy.allowedBuildModes or "normal") else "normal";
      nix_proxy_upstream =
        if nix_proxy_enabled then
          (nixProxy.upstream or "/nix/var/nix/daemon-socket/socket")
        else
          "/nix/var/nix/daemon-socket/socket";

      args_store_paths =
        let
          extractFromArg =
            arg':
            let
              arg = if builtins.isString arg' then { escaped = arg'; } else arg';
              vals = lib.filter builtins.isString (map (a: a.value) (lib.attrsToList arg));
              isStorePath = s: builtins.substring 0 11 s == "/nix/store/";
            in
            lib.filter isStorePath vals;
        in
        lib.unique (lib.concatMap extractFromArg args);

      closure_info =
        if paths != null then
          pkgs.closureInfo { rootPaths = paths ++ args_store_paths ++ [ inner_script ]; }
        else
          null;

      bind_types = {
        ro = "--ro-bind";
        ro_maybe = "--ro-bind-try";
        rw = "--bind";
        rw_maybe = "--bind-try";
        dev_maybe = "--dev-bind-try";
      };

      render_arg =
        arg':
        let
          arg = if builtins.isString arg' then { escaped = arg'; } else arg';
        in
        if !(arg.cond or true) then
          ""
        else if arg ? escaped then
          lib.escapeShellArg arg.escaped
        else if arg ? unescaped then
          arg.unescaped
        else if arg ? tmpfs then
          "--tmpfs ${arg.tmpfs}"
        else if arg ? setenv then
          "--setenv ${lib.escapeShellArg arg.setenv} ${lib.escapeShellArg arg.value}"
        else
          let
            kind = lib.findFirst (k: arg ? ${k}) null (builtins.attrNames bind_types);
          in
          if kind == null then
            throw "Unsupported bwrap argument: ${builtins.toJSON arg}"
          else
            "${bind_types.${kind}} ${arg.src or arg.${kind}} ${arg.${kind}}";

      bwrap_args = lib.concatMapStringsSep " " render_arg args;

      _ =
        lib.throwIf (nix_proxy_enabled && paths != null)
          "nixProxy is incompatible with paths";

      pasta_base =
        if pasta != null then
          pasta
        else if proxy_enabled then
          throw "proxy requires pasta"
        else
          null;

      static_tcp_forward = if pasta_base != null then (pasta_base.tcpForward or [ ]) else [ ];

      pasta_flags = lib.optionalString (pasta_base != null) (
        let
          hasUdp = pasta_base.udpForward or [ ] != [ ];

          tcp_ports =
            (lib.optional proxy_enabled "\"$_PROXY_PORT\"") ++ (lib.map toString static_tcp_forward);

          tcpFlags =
            if lib.length tcp_ports != 0 then "-T \"${lib.concatStringsSep "," tcp_ports}\"" else "-T none";
          udpFlags =
            if hasUdp then "-U ${lib.concatMapStringsSep "," toString pasta_base.udpForward}" else "-U none";
          extraFlags = lib.concatStringsSep " " (pasta_base.extraFlags or [ ]);
        in
        lib.concatStringsSep " " (
          lib.filter (s: s != "") [
            tcpFlags
            udpFlags
            extraFlags
          ]
        )
      );

      sandbox_tmp_setup = ''
        _SANDBOX_TMP="$(${pkgs.coreutils}/bin/mktemp -d)"
        _sandbox_cleanup() {
          ${lib.optionalString proxy_enabled ''
            if [ -n "''${_PROXY_PID:-}" ]; then
              kill "$_PROXY_PID" 2>/dev/null
              wait "$_PROXY_PID" 2>/dev/null
            fi
          ''}
          ${lib.optionalString nix_proxy_enabled ''
            if [ -n "''${_NIX_PROXY_PID:-}" ]; then
              kill "$_NIX_PROXY_PID" 2>/dev/null
              wait "$_NIX_PROXY_PID" 2>/dev/null
            fi
          ''}
          ${pkgs.coreutils}/bin/chmod -R u+w "$_SANDBOX_TMP" 2>/dev/null
          ${pkgs.coreutils}/bin/rm -rf "$_SANDBOX_TMP"
        }
        trap _sandbox_cleanup EXIT
      '';

      proxy_setup = lib.optionalString proxy_enabled (
        network.mkProxySetup ({
          allowlist = proxy_allow_list;
        })
      );

      nix_proxy_setup = lib.optionalString nix_proxy_enabled ''
        _NIX_PROXY_SOCK="$_SANDBOX_TMP/nix-proxy.sock"
        ${nix_proxy}/bin/nix-proxy \
          --listen "$_NIX_PROXY_SOCK" \
          --upstream ${lib.escapeShellArg nix_proxy_upstream} \
          --allowed-system-features ${lib.escapeShellArg nix_proxy_allowed_system_features} \
          --allowed-setting-overrides ${lib.escapeShellArg nix_proxy_allowed_setting_overrides} \
          --allowed-build-modes ${lib.escapeShellArg nix_proxy_allowed_build_modes} \
          >> "$_NIX_PROXY_LOG" 2>&1 &
        _NIX_PROXY_PID=$!
        for _i in $(${pkgs.coreutils}/bin/seq 1 50); do
          [ -S "$_NIX_PROXY_SOCK" ] && break
          ${pkgs.coreutils}/bin/sleep 0.1
        done
      '';

      nix_proxy_args = lib.optionalString nix_proxy_enabled ''--setenv NIX_REMOTE daemon --bind "$_NIX_PROXY_SOCK" /nix/var/nix/daemon-socket/socket'';

      nix_subset_setup = lib.optionalString (closure_info != null) ''
        mkdir -p "$_SANDBOX_TMP/store"
        while IFS= read -r _storepath; do
          ${pkgs.coreutils}/bin/cp -a --reflink=auto --no-preserve=ownership "$_storepath" "$_SANDBOX_TMP/store/"
        done < ${closure_info}/store-paths
      '';

      nix_subset_args = lib.optionalString (
        closure_info != null
      ) ''--ro-bind "$_SANDBOX_TMP/store" /nix/store'';

      pasta_cmd = lib.optionalString (
        pasta_base != null
      ) "${pkgs.passt}/bin/pasta --config-net ${pasta_flags} -- ";

      network_lockdown = lib.optionalString proxy_enabled ("${network.networkLockdownScript}");

      drop_net_cap = lib.optionalString proxy_enabled "--cap-drop ALL";

      bwrap_cmd = ''${pkgs.bubblewrap}/bin/bwrap ${bwrap_args} ${drop_net_cap} ${nix_subset_args} ${nix_proxy_args} ${inner_script} "$@"'';

      cmd_parts = [
        sandbox_tmp_setup
        proxy_setup
        nix_proxy_setup
        nix_subset_setup
        pasta_cmd
        network_lockdown
        bwrap_cmd
      ];
    in
    lib.concatStringsSep " " cmd_parts;

in
{
  inherit bubblewrap_helper;
}
