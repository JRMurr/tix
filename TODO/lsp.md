# LSP Responsiveness TODO

## Problem

The debouncing and timeout changes made the LSP less predictable:
- Autocomplete works sometimes but not always
- Semantic information gets weird during the debounce window

Root causes:
1. Global `Mutex<AnalysisState>` serializes all requests — completion blocks while inference runs
2. `with_analysis` returns `Ok(None)` before first analysis completes — editor sees "no completions"
3. Fresh-parse + stale-types mismatch — `pending_text` re-parse paired with old `check_result`

## rust-analyzer Architecture (Reference)

rust-analyzer also uses salsa. Key differences from tix:

| Concern | rust-analyzer | tix (current) |
|---------|--------------|----------------|
| Debouncing | No timer. Event coalescing: drain all pending edits, apply as one batch | 300ms timer per file |
| Cancellation | Salsa revision + panic-unwind. `apply_change` blocks until snapshots drop | Cooperative `AtomicBool` checked every 1024 constraints |
| Stale data | Never served. Cancelled requests retried or return `ContentModified` | Stale analysis served with fresh parse tree |
| Locking | No global lock. `AnalysisHost` (write, main thread) / `Analysis` snapshots (read, Arc-cloned) | Single `parking_lot::Mutex` for everything |
| Prioritization | 3-tier thread pools (Worker / LatencySensitive / Formatting) | All work on tokio tasks, no prioritization |
| Diagnostics | Computed only after quiescence (no pending edits/VFS loads) | Inline at end of debounce worker |

Sources:
- https://rust-analyzer.github.io/book/contributing/architecture.html
- https://rust-analyzer.github.io/blog/2020/07/20/three-architectures-for-responsive-ide.html
- https://matklad.github.io/2023/05/06/zig-language-server-and-cancellation.html
- https://github.com/rust-lang/rust-analyzer/pull/14888 (thread priority)
- https://github.com/rust-lang/rust-analyzer/pull/17157 (don't retry position-reliant requests)

## Planned Changes

### 1. Separate read lock from write lock

Replace `Mutex<AnalysisState>` with `RwLock`. Run inference outside the lock,
then take write lock only to swap in the new `FileAnalysis`. Request handlers
take read lock (non-blocking while inference runs on another file).

### 2. Never serve mismatched fresh-tree + stale-types

When `pending_text` exists (analysis hasn't caught up), completion should only
provide syntactic completions (attr names from parse tree, keywords). Don't
consult stale type info when the tree is fresher than the analysis. Predictable:
fast syntax completions while typing, full type-aware completions once analysis
finishes.

### 3. Return ContentModified instead of empty results

When `with_analysis` finds no cached result, return LSP error `-32801`
(`ContentModified`) instead of `Ok(None)`. Editor will retry shortly.

## Future / Larger Refactors

### Event coalescing instead of timer-based debounce

Remove the 300ms sleep. On `didChange`, store text and immediately start
analysis. Drain any additional pending edits before starting. Debounce only
diagnostics publication (quiescence check). Interactive requests always get
latest analysis.

### Snapshot-based architecture

Full rust-analyzer pattern: main thread owns DB, applies edits in-place. Each
request gets a cheap `Arc` snapshot. Edits cancel outstanding snapshots via
salsa revision counting. Eliminates mutex for reads entirely.

### Thread priority / request prioritization

Separate worker pools for background (diagnostics, cache priming) vs
interactive (completion, hover). Prevents long-running analysis from starving
user-facing requests.
