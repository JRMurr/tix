# Standalone NixOS module file — typed via tix.toml context.
{ config, lib, pkgs, ... }:
{
  enable = lib.mkEnableOption "my-service";
  package = lib.mkOption {};
  greeting = lib.id "hello";
}
