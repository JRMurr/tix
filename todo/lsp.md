# LSP

## Nested arg autocomplete doesn't work
`bubblewrap_helper { args = [ ] }` — cursor inside `args` list doesn't get element-type
completions, only top-level attr keys. Top-level completion works fine.

## did_change_configuration bypasses DashMap snapshots
When stubs change via `did_change_configuration`, `reload_registry` runs analysis via the
legacy `state.files` path. DashMap snapshots are never updated — handlers read stale data.

## Hover on multi-element attrpaths shows wrong type
rnix parses `a.foo.bar` as a single Select with a two-element attrpath. Hovering on any
element shows the overall result type rather than the intermediate type.
