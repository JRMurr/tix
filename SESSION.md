## Pending issues

- Regenerating `stubs/lib.tix` via `gen_lib_stubs.py` produces some invalid type signatures from newer noogle data (e.g. `{ [string] : a }`, pipe's pseudo-syntax). Needs manual overrides added for `attrVals`, `attrValues`, and other newly-broken signatures before regenerating. The `@source` emission code in `gen_lib_stubs.py` is correct and tested, but the stubs aren't regenerated yet due to these unrelated noogle data regressions.
