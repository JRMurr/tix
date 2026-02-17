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
| **Go to Definition** | Jump to let bindings, lambda params, imports |
| **Find References** | All uses of a name in the file |
| **Rename** | Refactor bindings and their references |
| **Inlay Hints** | Inline type annotations after binding names |
| **Document Symbols** | Outline of let bindings and lambda params |
| **Document Links** | Clickable `import` paths |
| **Semantic Tokens** | Syntax highlighting based on name kind |
| **Selection Range** | Smart expand/shrink selection |
| **Document Highlight** | Highlight all uses of the name under cursor |
| **Formatting** | Runs `nixfmt` |

## Editor setup

### VS Code

Install the [Nix IDE](https://marketplace.visualstudio.com/items?itemName=jnoortheen.nix-ide) extension, then point it at `tix-lsp` in your workspace or user settings:

```json
{
  "nix.enableLanguageServer": true,
  "nix.serverPath": "tix-lsp"
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

The LSP accepts configuration via `initializationOptions`:

```json
{
  "stubs": ["/path/to/extra/stubs"],
  "inlayHints": { "enable": true },
  "diagnostics": { "enable": true }
}
```
