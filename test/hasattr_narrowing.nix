# Realistic hasattr narrowing example: bubblewrap helper
#
# Demonstrates that `?` narrowing prevents false MissingField errors in
# chained `if arg ? field then arg.field ...` patterns — common in Nix
# code that dispatches on attrset shape.
let
  /** type: pkgs :: Pkgs */
  pkgs = import ./pkgs.nix;

  /** type: lib :: Lib */
  lib = import ./lib.nix;

  # ────────────────────────────────────────────────────────────
  # bubblewrap helper — the core hasattr narrowing exercise
  # ────────────────────────────────────────────────────────────

  bubblewrap_helper = { args, name, script }:
    let
      inner_script = pkgs.writeShellScript name script;

      bindTypes = {
        ro = "--ro-bind";
        ro_maybe = "--ro-bind-try";
        rw = "--bind";
        rw_maybe = "--bind-try";
        dev_maybe = "--dev-bind-try";
      };

      # Each arg can be:
      #   - A string (shorthand for { escaped = <string>; })
      #   - An attrset with one of: escaped, unescaped, tmpfs, setenv, or
      #     a bind-type key (ro, rw, etc.)
      #
      # The `?` operator narrows arg so that field access in each branch
      # succeeds without contaminating sibling branches.
      renderArg = arg':
        let arg = if builtins.isString arg' then { escaped = arg'; } else arg';
        in if !(arg.cond or true) then
          ""
        else if arg ? escaped then
          lib.escapeShellArg arg.escaped
        else if arg ? unescaped then
          arg.unescaped
        else if arg ? tmpfs then
          "--tmpfs ${arg.tmpfs}"
        else if arg ? setenv then
          "--setenv ${lib.escapeShellArg arg.setenv} ${
            lib.escapeShellArg arg.value
          }"
        else if arg ? ro then
          "${bindTypes.ro} ${arg.ro} ${arg.ro}"
        else if arg ? rw then
          "${bindTypes.rw} ${arg.rw} ${arg.rw}"
        else if arg ? ro_maybe then
          "${bindTypes.ro_maybe} ${arg.ro_maybe} ${arg.ro_maybe}"
        else if arg ? rw_maybe then
          "${bindTypes.rw_maybe} ${arg.rw_maybe} ${arg.rw_maybe}"
        else if arg ? dev_maybe then
          "${bindTypes.dev_maybe} ${arg.dev_maybe} ${arg.dev_maybe}"
        else
          builtins.throw "Unsupported bwrap argument: ${builtins.toJSON arg}";

      bwrap_args = lib.concatMapStringsSep " " renderArg args;

    in ''${pkgs.bubblewrap}/bin/bwrap ${bwrap_args} ${inner_script} "$@"'';

  # ────────────────────────────────────────────────────────────
  # Callers — exercise the helper at different "shapes"
  # ────────────────────────────────────────────────────────────

  # Simple caller: all string args (the isString shorthand path).
  simple_sandbox = bubblewrap_helper {
    name = "simple-sandbox";
    script = "echo hello";
    args = [
      "--die-with-parent"
      "--unshare-all"
    ];
  };

  # Caller with mixed arg shapes.
  mixed_sandbox = bubblewrap_helper {
    name = "mixed-sandbox";
    script = "exec $@";
    args = [
      { ro = "/nix/store"; }
      { rw = "/tmp"; }
      { tmpfs = "/run"; }
      { setenv = "HOME"; value = "/homeless-shelter"; }
      { unescaped = "--proc /proc"; }
      { escaped = "--new-session"; }
      { ro = "/etc/resolv.conf"; cond = true; }
    ];
  };

  # Caller that passes an arg with cond = false (skipped at runtime).
  conditional_sandbox = bubblewrap_helper {
    name = "conditional-sandbox";
    script = "ls /";
    args = [
      { ro = "/nix/store"; }
      { dev_maybe = "/dev/dri"; cond = false; }
    ];
  };

in {
  inherit simple_sandbox mixed_sandbox conditional_sandbox;
}
