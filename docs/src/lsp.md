# LSP

**TLDR:** `tix-lsp` provides IDE features over the Language Server Protocol. Run it, point your editor at it.

## Running

```bash
tix-lsp [--stubs path/to/stubs/] [--no-default-stubs]
```

Communicates over stdin/stdout. Same stub flags as `tix-cli`.

## Features

| Feature | What it does |
|---------|-------------|
| **Hover** | Shows inferred type and doc comments |
| **Completion** | Attrset field access (`.`), function args, identifiers, inherit targets |
| **Signature Help** | Parameter names and types when calling functions; highlights the active parameter for curried calls |
| **Go to Definition** | Jump to let bindings, lambda params, imports, and cross-file field definitions (including `callPackage`-style patterns) |
| **Find References** | All uses of a name in the file |
| **Rename** | Refactor bindings and their references; cross-file rename updates `x.field` select expressions in open files that import the renamed file |
| **Inlay Hints** | Inline type annotations after binding names |
| **Document Symbols** | Outline of let bindings and lambda params |
| **Document Links** | Clickable `import` paths |
| **Semantic Tokens** | Syntax highlighting based on name kind |
| **Selection Range** | Smart expand/shrink selection |
| **Document Highlight** | Highlight all uses of the name under cursor |
| **Formatting** | Runs `nixfmt` |
| **Diagnostics** | Type errors, missing fields, import resolution errors, inference timeouts |

## Diagnostics

When diagnostics are enabled (`"diagnostics": { "enable": true }`), tix reports:

- **Type errors** (ERROR): type mismatches, invalid operators, invalid attrset merges
- **Missing fields** (ERROR): accessing a field that doesn't exist on a closed attrset
- **Unresolved names** (WARNING): references to names that can't be resolved
- **Import errors** (WARNING): `import ./missing.nix` where the target file doesn't exist, cyclic imports, or errors in the imported file
- **Inference timeout** (WARNING): when type inference exceeds the 10-second deadline, partial results are still available for bindings inferred before the timeout

Import errors appear at the `import` expression so you can see which import failed and why. The CLI (`tix-cli`) shows the same diagnostics with source context.

## Editor setup

### VS Code

Install the [Nix IDE](https://marketplace.visualstudio.com/items?itemName=jnoortheen.nix-ide) extension, then configure it to use `tix-lsp`.

**Minimal setup** — add to your `.vscode/settings.json` (workspace) or user settings:

```json
{
  "nix.enableLanguageServer": true,
  "nix.serverPath": "tix-lsp"
}
```

**With extra stubs and initialization options:**

```json
{
  "nix.enableLanguageServer": true,
  "nix.serverPath": "tix-lsp",
  "nix.serverSettings": {
    "stubs": ["./my-stubs"],
    "inlayHints": { "enable": true },
    "diagnostics": { "enable": true }
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
      cmd = { "tix-lsp" },
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
