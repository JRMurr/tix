{ config, lib, ... }:
lib.mkIf config.services.pipewire.enable {
  services.pipewire.enable = true;
}
