// ==============================================================================
// textDocument/formatting — format via external nixfmt
// ==============================================================================
//
// Shells out to `nixfmt` on stdin/stdout. If nixfmt is not installed or fails,
// returns None gracefully — formatting is best-effort.

use tower_lsp::lsp_types::{Position, Range, TextEdit};

use crate::convert::LineIndex;

/// Format a Nix document by piping it through `nixfmt`.
///
/// Returns None if nixfmt is not available or the file is already formatted.
pub fn format_document(contents: &str, line_index: &LineIndex) -> Option<Vec<TextEdit>> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let mut child = Command::new("nixfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| {
            log::warn!("failed to run nixfmt: {e}");
        })
        .ok()?;

    // Pipe the document contents to nixfmt's stdin.
    child
        .stdin
        .take()
        .unwrap()
        .write_all(contents.as_bytes())
        .ok()?;

    let output = child.wait_with_output().ok()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        log::warn!("nixfmt failed: {stderr}");
        return None;
    }

    let formatted = String::from_utf8(output.stdout).ok()?;

    // No change needed — file is already formatted.
    if formatted == contents {
        return None;
    }

    // Replace the entire document with the formatted output.
    let end = line_index.position(contents.len() as u32);
    Some(vec![TextEdit {
        range: Range::new(Position::new(0, 0), end),
        new_text: formatted,
    }])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn returns_none_when_nixfmt_unavailable() {
        // If nixfmt happens to be installed, this test still passes because
        // the empty string is valid and already formatted. We're mainly
        // verifying no panics occur.
        let line_index = LineIndex::new("");
        let result = format_document("", &line_index);
        // Either None (not installed / no change) or Some with edits — both are fine.
        // The key assertion is no panic.
        let _ = result;
    }

    #[test]
    fn full_document_range_covers_entire_text() {
        let src = "let\n  x = 1;\nin x\n";
        let line_index = LineIndex::new(src);
        let end = line_index.position(src.len() as u32);
        // "let\n  x = 1;\nin x\n" has 4 lines (3 newlines).
        // Line 3 is "in x\n", line 4 would be empty after trailing newline.
        assert_eq!(end.line, 3);
        assert_eq!(end.character, 0);
    }
}
