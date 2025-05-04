# Tix

A very simple/basic type checker for nix.


## High level design

The rough structure of the type checker is using hindley milner type inference with some home grown extensions.
Hindley Milner on its own does not really handle operator overloading which causes issues for most of nix's binary operators.
I also want to support union types since that matches nix's dynamic nature more than something like type classes from haskell.

My "ideology" for the type checker is do as much inference as is reasonable but defer to comments with type annotations when it would be too hard to infer.
(Not sure how well the current impl follows that...)

Rough pipeline
- Parse program into ast `lang_ast/lower.rs`
- Do name resolution to roughly structure the ast to find variable dependencies/scopes `lang_ast/nameres.rs`
- Go over the grouped definitions "bottom up" and infer a group at a time `lang_check/infer.rs`


Inference Pipeline
- First for each expression generate constraints on what the variable could be
- After generating constraints solve them in one go
  - If a constraint could not be solved fully "defer it" to be solved in a higher up group
  - This is where "let generalization" happens

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