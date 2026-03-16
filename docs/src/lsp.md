# LSP

**TLDR:** `tix lsp` provides IDE features over the Language Server Protocol. Run it, point your editor at it.

## Running

```bash
tix lsp
```

Communicates over stdin/stdout. Stubs are loaded from `tix.toml` (auto-discovered from the workspace root) and editor settings.

## Features

| Feature | What it does |
|---------|-------------|
| **Hover** | Shows inferred type and doc comments |
| **Completion** | Attrset field access (`.`), function args, identifiers, inherit targets |
| **Signature Help** | Parameter names and types when calling functions; highlights the active parameter for curried calls |
| **Go to Definition** | Jump to let bindings, lambda params, imports, cross-file field definitions (including `callPackage`-style patterns), and any path literal (including directory→`default.nix` resolution) |
| **Go to Type Definition** | Jump to the `.tix` stub file where a type alias is declared. Works on any name or expression whose inferred type is a named alias (e.g. `Derivation`, `Lib`). Only available for stubs loaded from disk. |
| **Find References** | All uses of a name in the file |
| **Rename** | Refactor bindings and their references; cross-file rename updates `x.field` select expressions in open files that import the renamed file |
| **Inlay Hints** | Inline type annotations after binding names |
| **Document Symbols** | Outline of let bindings and lambda params |
| **Workspace Symbols** | Search for symbols across all open files |
| **Document Links** | Clickable `import` and `callPackage` paths |
| **Semantic Tokens** | Syntax highlighting based on name kind |
| **Selection Range** | Smart expand/shrink selection |
| **Document Highlight** | Highlight all uses of the name under cursor |
| **Code Actions** | Quick fixes: add missing field, add type annotation, remove unused binding |
| **Formatting** | Runs `nixfmt` |
| **Diagnostics** | Type errors, missing fields, import resolution errors, inference timeouts — each with a stable [error code](./diagnostics/index.md) |

## Diagnostics

When diagnostics are enabled (`"diagnostics": { "enable": true }`), tix reports:

- **Type errors** (ERROR): type mismatches ([E001](./diagnostics/e001.md)), invalid operators ([E003](./diagnostics/e003.md)), invalid attrset merges ([E004](./diagnostics/e004.md))
- **Missing fields** (ERROR): accessing a field that doesn't exist on a closed attrset ([E002](./diagnostics/e002.md))
- **Unresolved names** (WARNING): references to names that can't be resolved ([E005](./diagnostics/e005.md))
- **Import errors** (WARNING): `import ./missing.nix` where the target file doesn't exist ([E007](./diagnostics/e007.md)), angle bracket imports like `<nixpkgs>` ([E012](./diagnostics/e012.md)), or files that haven't been analyzed ([E013](./diagnostics/e013.md))
- **Inference timeout** (WARNING): when type inference exceeds the 10-second deadline ([E008](./diagnostics/e008.md))
- **Unknown type** (configurable): bindings whose type is `?` ([E014](./diagnostics/e014.md)) — default severity: hint

Every diagnostic has a stable error code (e.g. `E001`) that links to documentation. In VS Code, click the code in the Problems panel to open the docs page.

Import errors appear at the `import` expression so you can see which import failed and why. The CLI (`tix`) shows the same diagnostics with error codes in Rust-style format: `error[E001]: message`.

## Code Actions

Code actions (quick fixes / refactorings) are offered based on diagnostics and cursor position:

- **Add missing field** (quick fix): when you access a field that doesn't exist on a closed attrset (e.g. `x.bar` where `x = { foo = 1; }`), offers to insert `bar = throw "TODO";` into the attrset definition. Only works when the attrset definition is visible in the same file.

- **Add type annotation** (refactor): when the cursor is on a let-binding or rec-attrset field that has an inferred type, offers to insert a `/** type: name :: <type> */` doc comment above the binding. Skipped if an annotation already exists.

- **Remove unused binding** (quick fix): when a let-binding has no references in the file, offers to remove the entire `name = value;` line. Names starting with `_` are excluded (conventional "unused" prefix in Nix).

## Memory limit

The LSP sets a 4 GiB virtual address space limit (`RLIMIT_AS`) at startup to prevent runaway inference from consuming all system memory. Override with the `TIX_MEM_LIMIT` environment variable (value in MiB):

```bash
TIX_MEM_LIMIT=8192 tix lsp   # 8 GiB
TIX_MEM_LIMIT=0 tix lsp      # no limit
```

In addition to the hard `RLIMIT_AS` limit, the LSP monitors RSS (resident memory) and bails out of inference early when memory pressure is detected — returning partial results instead of crashing. This prevents the process from hitting the virtual address space limit (which would cause a hard SIGABRT). Background analysis of project files is also paused when RSS is high.

## Editor setup

### VS Code

Install the [Nix IDE](https://marketplace.visualstudio.com/items?itemName=jnoortheen.nix-ide) extension, then configure it to use `tix lsp`.

**Minimal setup** — add to your `.vscode/settings.json` (workspace) or user settings:

```json
{
  "nix.enableLanguageServer": true,
  "nix.serverPath": ["tix", "lsp"]
}
```

**With extra stubs and initialization options:**

```json
{
  "nix.enableLanguageServer": true,
  "nix.serverPath": ["tix", "lsp"],
  "nix.serverSettings": {
    "stubs": ["./my-stubs"],
    "inlayHints": { "enable": true },
    "diagnostics": { "enable": true, "unknownType": "hint" }
  }
}
```

### Neovim (nvim-lspconfig)

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "nix",
  callback = function()
    vim.lsp.start({
      name = "tix",
      cmd = { "tix", "lsp" },
    })
  end,
})
```

### Initialization options

The LSP accepts configuration via `initializationOptions`. How you pass these depends on your editor — in VS Code they go under `nix.serverSettings`, in Neovim they go in the `init_options` field of `vim.lsp.start()`:

```json
{
  "stubs": ["/path/to/extra/stubs"],
  "inlayHints": { "enable": true },
  "diagnostics": { "enable": true }
}
```
