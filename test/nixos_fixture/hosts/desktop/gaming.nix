{ pkgs, config, ... }:
{
  programs.steam.enable = true;
  programs.steam.remotePlay.enable = true;
}
