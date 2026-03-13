use std::path::PathBuf;

use serde::Deserialize;
use tower_lsp::lsp_types::DiagnosticSeverity;

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

/// Configurable severity level for optional diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiagnosticLevel {
    Off,
    Hint,
    Warning,
    Error,
}

impl DiagnosticLevel {
    /// Convert to an LSP DiagnosticSeverity. Returns `None` for `Off`.
    pub fn to_lsp_severity(self) -> Option<DiagnosticSeverity> {
        match self {
            DiagnosticLevel::Off => None,
            DiagnosticLevel::Hint => Some(DiagnosticSeverity::HINT),
            DiagnosticLevel::Warning => Some(DiagnosticSeverity::WARNING),
            DiagnosticLevel::Error => Some(DiagnosticSeverity::ERROR),
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DiagnosticsConfig {
    pub enable: bool,
    /// Severity for "unknown type" (`?`) diagnostics on non-param bindings.
    /// Default: Hint (least intrusive).
    pub unknown_type: DiagnosticLevel,
}

impl Default for DiagnosticsConfig {
    fn default() -> Self {
        Self {
            enable: true,
            unknown_type: DiagnosticLevel::Hint,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_level_from_json_camelcase() {
        let level: DiagnosticLevel = serde_json::from_str(r#""off""#).unwrap();
        assert_eq!(level, DiagnosticLevel::Off);

        let level: DiagnosticLevel = serde_json::from_str(r#""hint""#).unwrap();
        assert_eq!(level, DiagnosticLevel::Hint);

        let level: DiagnosticLevel = serde_json::from_str(r#""warning""#).unwrap();
        assert_eq!(level, DiagnosticLevel::Warning);

        let level: DiagnosticLevel = serde_json::from_str(r#""error""#).unwrap();
        assert_eq!(level, DiagnosticLevel::Error);
    }

    #[test]
    fn diagnostics_config_defaults() {
        let config: DiagnosticsConfig = serde_json::from_str("{}").unwrap();
        assert!(config.enable);
        assert_eq!(config.unknown_type, DiagnosticLevel::Hint);
    }

    #[test]
    fn diagnostics_config_with_unknown_type() {
        let config: DiagnosticsConfig =
            serde_json::from_str(r#"{"unknownType": "warning"}"#).unwrap();
        assert_eq!(config.unknown_type, DiagnosticLevel::Warning);
    }

    #[test]
    fn tix_config_with_diagnostics() {
        let config: TixConfig =
            serde_json::from_str(r#"{"diagnostics": {"enable": true, "unknownType": "error"}}"#)
                .unwrap();
        assert!(config.diagnostics.enable);
        assert_eq!(config.diagnostics.unknown_type, DiagnosticLevel::Error);
    }

    #[test]
    fn diagnostic_level_to_lsp_severity() {
        assert!(DiagnosticLevel::Off.to_lsp_severity().is_none());
        assert_eq!(
            DiagnosticLevel::Hint.to_lsp_severity(),
            Some(DiagnosticSeverity::HINT)
        );
        assert_eq!(
            DiagnosticLevel::Warning.to_lsp_severity(),
            Some(DiagnosticSeverity::WARNING)
        );
        assert_eq!(
            DiagnosticLevel::Error.to_lsp_severity(),
            Some(DiagnosticSeverity::ERROR)
        );
    }
}
