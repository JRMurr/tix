{ pkgs, config, ... }:
{
  programs.
  #        ^1
  programs.steam.enable = true;
  programs.steam.remotePlay.enable = true;
}
