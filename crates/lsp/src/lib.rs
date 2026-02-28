mod code_actions;
mod completion;
mod config;
pub mod convert;
mod diagnostics;
mod document_highlight;
mod document_link;
mod document_symbol;
mod formatting;
mod goto_def;
mod hover;
mod inlay_hint;
#[cfg(test)]
mod pbt;
pub(crate) mod project_config;
mod references;
mod rename;
mod selection_range;
mod semantic_tokens;
pub mod server;
mod signature_help;
mod state;
pub mod test_util;
mod ty_nav;
mod workspace_symbols;

use lang_check::aliases::TypeAliasRegistry;

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
pub fn load_stubs(
    registry: &mut TypeAliasRegistry,
    path: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                load_stubs(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                let source = std::fs::read_to_string(&entry_path)?;
                let file = comment_parser::parse_tix_file(&source)
                    .map_err(|e| format!("Error parsing {}: {e}", entry_path.display()))?;
                registry.load_tix_file(&file);
            }
        }
    } else {
        let source = std::fs::read_to_string(path)?;
        let file = comment_parser::parse_tix_file(&source)
            .map_err(|e| format!("Error parsing {}: {e}", path.display()))?;
        registry.load_tix_file(&file);
    }
    Ok(())
}
