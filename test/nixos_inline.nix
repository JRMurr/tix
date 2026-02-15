# Inline NixOS module with doc comment context annotation.
{
  nixosModules.default =
    /** context: nixos */
    { config, lib, pkgs, ... }: {
      enable = lib.mkEnableOption "my-service";
      greeting = lib.id "hello";
    };
}
