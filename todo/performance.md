# Performance

## Reduce allocations in hot-path constraint propagation
1. Bounds cloned on every constraint propagation (`constrain.rs:127-131`) — index-based
   iteration would avoid this.
2. TypeAliasRegistry cloned twice per file analysis — `Arc` would make this free.
3. Full Expr clone on every infer_expr_inner call — could match on `&Expr` instead.
4. Bindings::get() is O(n) linear scan (has FIXME).
