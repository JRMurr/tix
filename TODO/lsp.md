# LSP

## ~~Nested arg autocomplete doesn't work~~ (Fixed)
Expected-type-aware completion now resolves the expected type at cursor by walking
up the syntax tree to the callsite, then down through the function's parameter type.
For unions, suggests fields from ALL variants. Filters already-present fields.

## did_change_configuration bypasses DashMap snapshots
When stubs change via `did_change_configuration`, `reload_registry` runs analysis via the
legacy `state.files` path. DashMap snapshots are never updated — handlers read stale data.

## Hover on multi-element attrpaths shows wrong type
rnix parses `a.foo.bar` as a single Select with a two-element attrpath. Hovering on any
element shows the overall result type rather than the intermediate type.
