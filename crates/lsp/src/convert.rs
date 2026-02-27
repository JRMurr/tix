// ==============================================================================
// LineIndex: rowan TextRange <-> LSP Position/Range conversion
// ==============================================================================
//
// Builds a line-start offset table from source text, then converts between
// byte offsets (used by rowan/rnix) and LSP line/character positions.
//
// Simplification: assumes ASCII (character offset == byte offset within a line).
// This is fine for Nix source code which is overwhelmingly ASCII.

use tower_lsp::lsp_types::{Position, Range};

/// Pre-computed line start byte offsets for fast offset <-> position conversion.
#[derive(Clone)]
pub struct LineIndex {
    /// Byte offset of the start of each line (line 0 starts at offset 0).
    line_starts: Vec<u32>,
    /// Total length of the source text in bytes.
    len: u32,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, byte) in text.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        LineIndex {
            line_starts,
            len: text.len() as u32,
        }
    }

    /// Convert a byte offset to an LSP Position (0-indexed line and character).
    pub fn position(&self, offset: u32) -> Position {
        let offset = offset.min(self.len);
        // Binary search for the line containing this offset.
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,      // Exact match: offset is at a line start.
            Err(next) => next - 1, // Between two line starts: use the preceding line.
        };
        let col = offset - self.line_starts[line];
        Position::new(line as u32, col)
    }

    /// Convert an LSP Position to a byte offset.
    pub fn offset(&self, pos: Position) -> u32 {
        let line = pos.line as usize;
        let line_start = if line < self.line_starts.len() {
            self.line_starts[line]
        } else {
            // Position beyond end of file — clamp to end of file.
            return self.len;
        };
        // Clamp the resulting offset to end of file to avoid producing
        // out-of-range byte offsets from invalid character positions.
        (line_start + pos.character).min(self.len)
    }

    /// Convert a rowan TextRange to an LSP Range.
    pub fn range(&self, text_range: rowan::TextRange) -> Range {
        Range::new(
            self.position(text_range.start().into()),
            self.position(text_range.end().into()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_line() {
        let idx = LineIndex::new("hello");
        assert_eq!(idx.position(0), Position::new(0, 0));
        assert_eq!(idx.position(3), Position::new(0, 3));
    }

    #[test]
    fn multi_line() {
        let idx = LineIndex::new("abc\ndef\nghi");
        // Line 0: "abc\n" starts at 0
        // Line 1: "def\n" starts at 4
        // Line 2: "ghi"   starts at 8
        assert_eq!(idx.position(0), Position::new(0, 0));
        assert_eq!(idx.position(4), Position::new(1, 0));
        assert_eq!(idx.position(5), Position::new(1, 1));
        assert_eq!(idx.position(8), Position::new(2, 0));
    }

    #[test]
    fn roundtrip() {
        let idx = LineIndex::new("let\n  x = 1;\nin x");
        let pos = Position::new(1, 2);
        let offset = idx.offset(pos);
        assert_eq!(idx.position(offset), pos);
    }

    #[test]
    fn offset_past_eof_clamps_to_end() {
        let idx = LineIndex::new("abc\ndef"); // len = 7
                                              // Line 99 doesn't exist — should clamp to end of file.
        assert_eq!(idx.offset(Position::new(99, 0)), 7);
    }

    #[test]
    fn offset_character_past_line_end_clamps() {
        let idx = LineIndex::new("ab\ncd"); // len = 5
                                            // Line 0 has 2 chars + newline. character=100 should clamp to EOF.
        assert_eq!(idx.offset(Position::new(0, 100)), 5);
    }

    #[test]
    fn position_past_eof_clamps() {
        let idx = LineIndex::new("abc"); // len = 3
                                         // Offset 10 is past EOF — should clamp to end.
        assert_eq!(idx.position(10), Position::new(0, 3));
    }
}
