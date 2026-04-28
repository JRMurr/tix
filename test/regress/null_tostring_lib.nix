# Library function with optional `? null` parameter consumed by toString.
# Bug: across file boundaries, the param's exported type collapsed to `null`
# because toString is fully polymorphic (`a -> string`) and gives the param
# no concrete upper bound — the empty-fallback then expanded the default's
# `null` lower bound into the negative position.
{ modules ? null }:
builtins.toString modules
