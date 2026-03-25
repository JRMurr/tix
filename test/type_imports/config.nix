# Pure type export example — no typeof, no inference needed.
#
# Declares a Config type alias in a doc comment. Other files can import it
# via import("./config.nix").Config without triggering any inference.

/**
  type Config = { name: string, debug: bool, port: int, ... };
*/
{ name, debug ? false, port ? 8080, ... }:
{
    greeting = "Hello, ${name}!";
    is_debug = debug;
    listen_port = port;
}
