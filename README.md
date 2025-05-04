# Tix

A very simple/basic type checker for nix.



## links
- https://github.com/oxalica/nil
  - does some level of type inference but doest support annotations (at least for now)
  - read over its source a lot and took some code from there to get started
  - Long term would be nice to merge into their. For now re-implementing for my own understanding and ease of messing around
- https://github.com/nix-community/nixdoc stole some parsing logic from there
- [nix types rfc](https://github.com/hsjobeki/nix-types/blob/main/docs/README.md#nix-types-rfc-draft)
  - good spec for parsing doc comments
- https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf
  - An approach to hash expressions that is used here to hash our type representation
  - hashing a type makes it easy to see if two types are basically the same when they are in a union together