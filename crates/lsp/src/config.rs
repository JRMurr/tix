use std::path::PathBuf;

use serde::Deserialize;

/// Runtime configuration for the Tix LSP, populated from `initializationOptions`
/// and `workspace/didChangeConfiguration`.
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TixConfig {
    /// Paths to `.tix` stub files or directories (loaded in addition to CLI stubs).
    pub stubs: Vec<PathBuf>,
    pub inlay_hints: InlayHintsConfig,
    pub diagnostics: DiagnosticsConfig,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct InlayHintsConfig {
    pub enable: bool,
}

impl Default for InlayHintsConfig {
    fn default() -> Self {
        Self { enable: true }
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DiagnosticsConfig {
    pub enable: bool,
}

impl Default for DiagnosticsConfig {
    fn default() -> Self {
        Self { enable: true }
    }
}
