// ==============================================================================
// LineIndex: rowan TextRange <-> LSP Position/Range conversion
// ==============================================================================
//
// Builds a line-start offset table from source text, then converts between
// byte offsets (used by rowan/rnix) and LSP line/character positions.
//
// LSP spec defines Position.character as UTF-16 code units. We store the
// source text so we can iterate chars and count UTF-16 widths accurately.
// For pure-ASCII text (the common case for Nix), this degrades to a simple
// subtraction since every ASCII char is 1 UTF-16 code unit.

use tower_lsp::lsp_types::{Position, Range};

/// Pre-computed line start byte offsets for fast offset <-> position conversion.
#[derive(Clone)]
pub struct LineIndex {
    /// Source text, retained for UTF-16 column conversion.
    text: String,
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
            text: text.to_owned(),
            line_starts,
            len: text.len() as u32,
        }
    }

    /// Convert a byte offset to an LSP Position (0-indexed line and UTF-16
    /// character offset).
    pub fn position(&self, offset: u32) -> Position {
        let offset = offset.min(self.len);
        // Binary search for the line containing this offset.
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,      // Exact match: offset is at a line start.
            Err(next) => next - 1, // Between two line starts: use the preceding line.
        };
        let line_start = self.line_starts[line] as usize;
        let target = offset as usize;

        // Count UTF-16 code units from line start to the target byte offset.
        let line_slice = &self.text[line_start..target];
        let utf16_col: u32 = line_slice.chars().map(|c| c.len_utf16() as u32).sum();

        Position::new(line as u32, utf16_col)
    }

    /// Convert an LSP Position (UTF-16 character offset) to a byte offset.
    pub fn offset(&self, pos: Position) -> u32 {
        let line = pos.line as usize;
        let line_start = if line < self.line_starts.len() {
            self.line_starts[line] as usize
        } else {
            // Position beyond end of file — clamp to end of file.
            return self.len;
        };

        // Walk chars from line start, counting UTF-16 code units until we've
        // consumed `pos.character` units (or hit end-of-line/file).
        let remaining = &self.text[line_start..];
        let mut utf16_consumed: u32 = 0;
        let mut byte_offset = line_start;
        for ch in remaining.chars() {
            if ch == '\n' || utf16_consumed >= pos.character {
                break;
            }
            utf16_consumed += ch.len_utf16() as u32;
            byte_offset += ch.len_utf8();
        }

        (byte_offset as u32).min(self.len)
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
                                            // Line 0 has 2 chars + newline. character=100 should clamp to end of
                                            // line 0 (byte 2, just before the newline), not EOF.
        assert_eq!(idx.offset(Position::new(0, 100)), 2);
    }

    #[test]
    fn position_past_eof_clamps() {
        let idx = LineIndex::new("abc"); // len = 3
                                         // Offset 10 is past EOF — should clamp to end.
        assert_eq!(idx.position(10), Position::new(0, 3));
    }

    // UTF-16 encoding tests: LSP positions use UTF-16 code units, not bytes.

    #[test]
    fn multibyte_2byte_utf8_position() {
        // 'ö' is 2 bytes in UTF-8 but 1 UTF-16 code unit.
        // "aöb" = bytes [a(1), ö(2), b(1)] = 4 bytes total
        // byte offset 3 points to 'b', which is character index 2 in UTF-16.
        let idx = LineIndex::new("aöb");
        assert_eq!(idx.position(3), Position::new(0, 2));
    }

    #[test]
    fn emoji_surrogate_pair_position() {
        // '😀' is 4 bytes in UTF-8 but 2 UTF-16 code units (surrogate pair).
        // "a😀b" = bytes [a(1), 😀(4), b(1)] = 6 bytes total
        // byte offset 5 points to 'b', which is character index 3 in UTF-16
        // (1 for 'a' + 2 for '😀' surrogate pair).
        let idx = LineIndex::new("a😀b");
        assert_eq!(idx.position(5), Position::new(0, 3));
    }

    #[test]
    fn multibyte_offset_roundtrip() {
        // Round-trip: position → offset → position should be identity.
        let idx = LineIndex::new("aöb");
        let pos = idx.position(3); // 'b' at byte 3
        assert_eq!(pos, Position::new(0, 2));
        let offset = idx.offset(pos);
        assert_eq!(offset, 3);
    }

    #[test]
    fn emoji_offset_roundtrip() {
        let idx = LineIndex::new("a😀b");
        let pos = idx.position(5); // 'b' at byte 5
        assert_eq!(pos, Position::new(0, 3));
        let offset = idx.offset(pos);
        assert_eq!(offset, 5);
    }

    #[test]
    fn multibyte_multiline() {
        // Line 0: "héllo\n" (h=1, é=2, llo=3, \n=1 → 7 bytes)
        // Line 1: "w😀rld"  (w=1, 😀=4, rld=3 → 8 bytes)
        let idx = LineIndex::new("héllo\nw😀rld");
        // 'l' after 'é' on line 0: byte offset 4, UTF-16 col 3
        assert_eq!(idx.position(4), Position::new(0, 3));
        // '😀' on line 1: byte offset 8, UTF-16 col 1
        assert_eq!(idx.position(8), Position::new(1, 1));
        // 'r' after '😀' on line 1: byte offset 12, UTF-16 col 3
        assert_eq!(idx.position(12), Position::new(1, 3));
    }
}
