{ config, lib, ... }:
{
  programs.bash.enable = true;
  programs.git.enable = true;
  programs.git.userName = "Test User";
}
