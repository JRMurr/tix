{ 
  # type: pkgs :: Pkgs
  pkgs
}:
let
  lib = pkgs.lib;

  bubblewrap_helper =
    {
      args,
      name,
      script,
      pasta ? null,
      paths ? null,
    }:
    let
      inner_script = pkgs.writeShellScript name script;

      bindTypes = {
        ro = "--ro-bind";
        ro_maybe = "--ro-bind-try";
        rw = "--bind";
        rw_maybe = "--bind-try";
        dev_maybe = "--dev-bind-try";
      };

      renderArg =
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
            # Find which bind type this arg uses
            kind = lib.findFirst (k: arg ? ${k}) null (builtins.attrNames bindTypes);
          in
          if kind == null then
            throw "Unsupported bwrap argument: ${builtins.toJSON arg}"
          else
            "${bindTypes.${kind}} ${arg.src or arg.${kind}} ${arg.${kind}}";
      bwrap_args = lib.concatMapStringsSep " " renderArg args;

      # Build pasta flags from the config
      # -t none / -u none: disable automatic mapping of all host listeners
      # -T / -U: explicitly forward only the specified ports into the namespace
      pastaFlags = lib.optionalString (pasta != null) (
        let
          hasTcp = pasta.tcpForward or [ ] != [ ];
          hasUdp = pasta.udpForward or [ ] != [ ];
          tcpFlags =
            if hasTcp then "-t none -T ${lib.concatMapStringsSep "," toString pasta.tcpForward}" else "-t none";
          udpFlags =
            if hasUdp then "-u none -U ${lib.concatMapStringsSep "," toString pasta.udpForward}" else "-u none";
          extraFlags = lib.concatStringsSep " " (pasta.extraFlags or [ ]);
        in
        lib.concatStringsSep " " (
          lib.filter (s: s != "") [
            tcpFlags
            udpFlags
            extraFlags
          ]
        )
      );
      bwrap_cmd = ''${pkgs.bubblewrap}/bin/bwrap ${bwrap_args} ${inner_script} "$@"'';

      main_cmd =
        if pasta == null then
          bwrap_cmd
        else
          "${pkgs.passt}/bin/pasta --config-net ${pastaFlags} -- ${bwrap_cmd}";

    in
    "${main_cmd}";
in
{
  inherit bubblewrap_helper;
}
