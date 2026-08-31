# Session notes

- `Warning::AnnotationParseError` (lang_check/src/lib.rs:1285) appears unreachable: `comment.pest`'s `comment_content` rule accepts any text (`other_text` swallows what `type_block` rejects), so `parse_and_collect` never returns `Err`. Consider removing the variant or making the grammar strict inside a started `type:` block.
- rowan 0.15 green-tree Drop is unguarded recursion: deep nesting (~25k on 8MB stack) overflows in the tree's destructor regardless of our stacker guards. Caps how deep an input tix can survive; would need an iterative drop upstream or leaking the tree.
- `analyze` in lang_ty/simplify.rs is still uncached over the hash-consed DAG (potentially exponential on shared nodes). Caching by (TyRef, polarity) is UNSOUND: occurrence paths are semantic for co-occurrence grouping — skipping shared-subtree re-visits can make distinct vars' occurrence sets spuriously equal and merge them. Needs a path-independent occurrence representation to fix.
