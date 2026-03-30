# @source annotation: remaining work

Branch: `source-annotations` (3 commits on top of `main`)

The `@source` infrastructure is complete and tested. What remains is wiring
the last-mile connections so generated stubs actually carry `@source` annotations
at runtime.

## 1. Add `--source-root` CLI flag to `tix gen-stubs`

**Files:** `crates/cli/src/main.rs`, `crates/cli/src/gen_stubs.rs`

The `CommonOptions.source_roots` and `PkgsOptions.source_roots` fields exist
but are always `Vec::new()` because no CLI flag populates them.

Add a clap arg to `CommonGenStubsArgs` (main.rs ~line 182):
```rust
/// Source root for @source annotations. Format: id=path (e.g. nixpkgs=/nix/store/...-source).
/// Can be repeated for multiple roots.
#[arg(long = "source-root", value_parser = parse_source_root)]
source_roots: Vec<(String, PathBuf)>,
```

Write `parse_source_root` value parser that splits on `=`:
```rust
fn parse_source_root(s: &str) -> Result<(String, PathBuf), String> {
    let (id, path) = s.split_once('=').ok_or("expected id=path")?;
    Ok((id.to_string(), PathBuf::from(path)))
}
```

Thread through the `From<CommonGenStubsArgs>` impl (main.rs ~line 214) and the
`Pkgs` arm (main.rs ~line 398).

## 2. Pass `--source-root` in `generate-stubs-runtime.nix`

**File:** `nix/generate-stubs-runtime.nix` (lines 222-225)

The nix expression already has `nixpkgs-path` and `home-manager-path` in scope.
Update the tix invocations to pass source roots:

```nix
./tix gen-stubs nixos --from-json ${nixosJsonFile} --descriptions \
  --source-root nixpkgs=${nixpkgs-path} -o $out/nixos.tix

./tix gen-stubs pkgs --from-json ${pkgsJsonFile} \
  --source-root nixpkgs=${nixpkgs-path} -o $out/pkgs.tix

# home-manager: pass both roots since HM modules can reference nixpkgs paths
./tix gen-stubs home-manager --from-json ${hmJsonFile} --descriptions \
  --source-root nixpkgs=${nixpkgs-path} \
  --source-root home-manager=${home-manager-path} -o $out/home-manager.tix
```

## 3. Emit `@source` on NixOS/HM option fields

**File:** `crates/cli/src/gen_stubs.rs`, function `options_to_attrset_ty_inner` (~line 364)

Currently this function generates attrset fields for options but doesn't emit
`@source`. The `OptionLeaf.pos` and `NamespaceNode.pos` fields are already
deserialized from JSON (added in this branch).

Changes needed:
- Add `source_roots: &[(String, PathBuf)]` parameter to
  `options_to_attrset_ty_inner`, `options_to_attrset_ty`, and
  `options_to_attrset_ty_with_docs`
- Before each field's `##` doc comment block (~line 398), call
  `format_source_annotation()` if `leaf.pos` is present
- The grammar already supports `@source` on `named_field` (added in this branch)
- Thread source_roots through from `run_nixos`/`run_home_manager` entry points
  (they get it from `CommonOptions.source_roots`)
- Remove the `#[allow(dead_code)]` on `CommonOptions.source_roots` (line 582)

Note: `options_to_attrset_ty` is a public API used from the LSP too (for inline
option type rendering). The LSP calls don't need source roots — pass `&[]` there.

## 4. Fix noogle data regressions and regenerate `stubs/lib.tix`

**Files:** `scripts/gen_lib_stubs.py`, `stubs/lib.tix`

Running `python3 scripts/gen_lib_stubs.py > stubs/lib.tix` produces some
invalid type signatures from newer noogle data. The `@source` emission code
is correct and tested, but the stubs can't be regenerated until overrides are
added for the broken entries.

Known broken noogle signatures (run the script and parse the output to find all):
- `attrVals`: noogle gives `{ [string] : a }` syntax (`.tix` wants `{ _: a, ... }`)
- `attrValues`: same issue
- `pipe`: pseudo-syntax `(a -> b) (b -> c) ...` (already overridden for trivial module)
- Possibly others — generate to a temp file and run `tix --no-default-stubs --stubs /tmp/test.tix /dev/null` to find parse errors

For each broken entry, add an override to `MANUAL_OVERRIDES` in gen_lib_stubs.py
(~line 47). Then regenerate and verify all 1370 tests still pass.

## 5. Update documentation

**File:** `docs/src/stubs.md`

Document the `@source` annotation syntax:
- Format: `@source <source-id>:<relative-path>:<line>:<column>`
- Examples: `@source nixpkgs:lib/trivial.nix:61:8`
- Placement: before `val`, `type`, or `module` declarations (after `##` doc block)
- Also allowed on attrset fields (for option stubs)
- Effect: jump-to-definition lands in the original source when the corresponding
  source root is configured
- Source roots configured automatically via `[stubs.generate]` in `tix.toml`

## Architecture reference

Key files for context:

| File | What it does |
|------|-------------|
| `crates/comment_parser/src/tix_decl.pest` | Grammar: `source_annotation` rule |
| `crates/comment_parser/src/tix_collect.rs` | Parser: `take_source_annotation()`, `parse_source_loc()` |
| `crates/comment_parser/src/lib.rs` | `SourceLocation` struct, `TixDeclaration.source` field |
| `crates/lang_check/src/aliases.rs` | `DeclLocation.source`, `TypeAliasRegistry.source_roots` |
| `crates/lsp/src/goto_def.rs` | `resolve_source_location()`, `decl_location_to_lsp()` (pub(crate)) |
| `crates/lsp/src/type_def.rs` | `resolve_decl_locations()` uses goto_def's resolver |
| `crates/lsp/src/store_stubs.rs` | `GeneratedStubs` returns source roots from nixpkgs/hm paths |
| `crates/cli/src/gen_stubs.rs` | `NixPosition`, `format_source_annotation()`, `maybe_emit_source()` |
| `nix/generate-stubs-runtime.nix` | `classifySet` captures `unsafeGetAttrPos` |
| `tools/extract-options.nix` | `walkOptions` captures `unsafeGetAttrPos` |
| `scripts/gen_lib_stubs.py` | `extract_source_loc()` from noogle lambda/attr_position |

Flow: Nix extracts positions → JSON → Rust strips store prefix using `--source-root` →
emits `@source id:path:line:col` in `.tix` → parser stores `SourceLocation` →
registry stores in `DeclLocation.source` → LSP resolves against `source_roots` →
jumps to original source file.
