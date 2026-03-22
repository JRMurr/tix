// ==============================================================================
// JSON Output Mode
// ==============================================================================
//
// Machine-readable JSON output for diagnostics, bindings, and root types.
// Used by `--format json` in both single-file and project (`tix check`) modes.

use std::collections::BTreeMap;
use std::path::Path;

use lang_ast::ModuleSourceMap;
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use rowan::ast::AstNode;
use serde::Serialize;

// ==============================================================================
// LineIndex — byte offset to 1-indexed (line, column)
// ==============================================================================

/// Minimal line index for converting byte offsets to 1-indexed (line, column).
/// Column is measured in UTF-8 characters (not bytes), matching editor behavior.
pub struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, byte) in text.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        LineIndex { line_starts }
    }

    /// Returns `(line, column)`, both 1-indexed.
    /// Column counts UTF-8 characters from the start of the line.
    pub fn line_col(&self, text: &str, byte_offset: u32) -> (u32, u32) {
        let byte_offset = byte_offset.min(text.len() as u32);
        let line_idx = match self.line_starts.binary_search(&byte_offset) {
            Ok(exact) => exact,
            Err(insert) => insert.saturating_sub(1),
        };
        let line_start = self.line_starts[line_idx] as usize;
        let byte_offset = byte_offset as usize;
        let col_chars = text[line_start..byte_offset].chars().count();
        ((line_idx + 1) as u32, (col_chars + 1) as u32)
    }
}

// ==============================================================================
// JSON Schema Types
// ==============================================================================

#[derive(Serialize)]
pub struct JsonOutput {
    pub version: u32,
    pub files: Vec<JsonFileResult>,
    pub summary: JsonSummary,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bindings: Option<BTreeMap<String, String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_type: Option<String>,
}

#[derive(Serialize)]
pub struct JsonFileResult {
    pub file: String,
    pub diagnostics: Vec<JsonDiagnostic>,
}

#[derive(Serialize)]
pub struct JsonDiagnostic {
    pub severity: &'static str,
    pub code: String,
    pub message: String,
    pub line: u32,
    pub column: u32,
    pub end_line: u32,
    pub end_column: u32,
    pub url: String,
}

#[derive(Serialize)]
pub struct JsonSummary {
    pub files_checked: usize,
    pub errors: usize,
    pub warnings: usize,
}

// ==============================================================================
// Diagnostic Conversion
// ==============================================================================

/// Convert diagnostics for a single file into JSON format.
/// Returns `(file_result, error_count, warning_count)`.
pub fn diagnostics_to_json(
    file_path: &Path,
    source_text: &str,
    diagnostics: &[TixDiagnostic],
    source_map: &ModuleSourceMap,
) -> (JsonFileResult, usize, usize) {
    let line_index = LineIndex::new(source_text);
    let root = rnix::Root::parse(source_text).tree();
    let mut error_count = 0;
    let mut warning_count = 0;
    let mut json_diags = Vec::with_capacity(diagnostics.len());

    for diag in diagnostics {
        let is_warning = diag.kind.is_warning();
        if is_warning {
            warning_count += 1;
        } else {
            error_count += 1;
        }

        // Resolve span: DuplicateKey has its own AstPtr spans, others use ExprId.
        let (start_offset, end_offset) =
            if let TixDiagnosticKind::DuplicateKey { second, .. } = &diag.kind {
                // Point at the duplicate (second) definition.
                let node = second.to_node(root.syntax());
                let range = node.text_range();
                (u32::from(range.start()), u32::from(range.end()))
            } else {
                source_map
                    .node_for_expr(diag.at_expr)
                    .map(|ptr| {
                        let node = ptr.to_node(root.syntax());
                        let range = node.text_range();
                        (u32::from(range.start()), u32::from(range.end()))
                    })
                    .unwrap_or((0, 0))
            };

        let (line, column) = line_index.line_col(source_text, start_offset);
        let (end_line, end_column) = line_index.line_col(source_text, end_offset);

        json_diags.push(JsonDiagnostic {
            severity: if is_warning { "warning" } else { "error" },
            code: diag.kind.code().to_string(),
            message: diag.kind.to_string(),
            line,
            column,
            end_line,
            end_column,
            url: diag.kind.docs_url(),
        });
    }

    let result = JsonFileResult {
        file: file_path.display().to_string(),
        diagnostics: json_diags,
    };

    (result, error_count, warning_count)
}

/// Serialize the JSON output to stdout.
pub fn write_json_output(output: &JsonOutput) -> Result<(), Box<dyn std::error::Error>> {
    serde_json::to_writer_pretty(std::io::stdout().lock(), output)?;
    println!();
    Ok(())
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_single_line() {
        let text = "hello world";
        let idx = LineIndex::new(text);
        assert_eq!(idx.line_col(text, 0), (1, 1));
        assert_eq!(idx.line_col(text, 5), (1, 6));
        assert_eq!(idx.line_col(text, 11), (1, 12));
    }

    #[test]
    fn line_col_multi_line() {
        let text = "abc\ndef\nghi";
        let idx = LineIndex::new(text);
        // 'a' at offset 0
        assert_eq!(idx.line_col(text, 0), (1, 1));
        // 'c' at offset 2
        assert_eq!(idx.line_col(text, 2), (1, 3));
        // '\n' at offset 3
        assert_eq!(idx.line_col(text, 3), (1, 4));
        // 'd' at offset 4
        assert_eq!(idx.line_col(text, 4), (2, 1));
        // 'g' at offset 8
        assert_eq!(idx.line_col(text, 8), (3, 1));
        // 'i' at offset 10
        assert_eq!(idx.line_col(text, 10), (3, 3));
    }

    #[test]
    fn line_col_clamps_past_eof() {
        let text = "ab";
        let idx = LineIndex::new(text);
        // Past end of text — clamped to end
        assert_eq!(idx.line_col(text, 100), (1, 3));
    }

    #[test]
    fn line_col_empty_text() {
        let text = "";
        let idx = LineIndex::new(text);
        assert_eq!(idx.line_col(text, 0), (1, 1));
    }

    #[test]
    fn line_col_multibyte_chars() {
        // "é" is 2 bytes in UTF-8, column should count chars not bytes
        let text = "éb";
        let idx = LineIndex::new(text);
        assert_eq!(idx.line_col(text, 0), (1, 1)); // start of 'é'
        assert_eq!(idx.line_col(text, 2), (1, 2)); // 'b' at byte 2, char col 2
        assert_eq!(idx.line_col(text, 3), (1, 3)); // past 'b'
    }

    #[test]
    fn line_col_at_newline_boundary() {
        let text = "a\nb";
        let idx = LineIndex::new(text);
        // At the newline itself (offset 1)
        assert_eq!(idx.line_col(text, 1), (1, 2));
        // After the newline (offset 2)
        assert_eq!(idx.line_col(text, 2), (2, 1));
    }

    #[test]
    fn json_output_serializes_without_optional_fields() {
        let output = JsonOutput {
            version: 1,
            files: vec![],
            summary: JsonSummary {
                files_checked: 0,
                errors: 0,
                warnings: 0,
            },
            bindings: None,
            root_type: None,
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(!json.contains("bindings"));
        assert!(!json.contains("root_type"));
    }

    #[test]
    fn json_output_serializes_with_optional_fields() {
        let mut bindings = BTreeMap::new();
        bindings.insert("x".to_string(), "int".to_string());
        let output = JsonOutput {
            version: 1,
            files: vec![],
            summary: JsonSummary {
                files_checked: 1,
                errors: 0,
                warnings: 0,
            },
            bindings: Some(bindings),
            root_type: Some("int".to_string()),
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains("\"bindings\""));
        assert!(json.contains("\"root_type\""));
        assert!(json.contains("\"x\""));
    }
}
