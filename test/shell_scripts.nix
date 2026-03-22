{
  # type: pkgs :: Pkgs
  pkgs,
}:

let

  foo = pkgs.writeShellScript "foo.sh" ''
    echo "foo"
  '';

  barScript = pkgs.writeShellScript "evaluate-my-file.sh" ''
    echo "bar"
  '';

  combine =
    {
      include_bar ? false,
    }:
    let
      bar = pkgs.lib.optionalString include_bar barScript;

    in
    ''
      ${foo}
      ${bar}
    '';

in
combine
