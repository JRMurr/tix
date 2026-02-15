// ==============================================================================
// textDocument/semanticTokens/full — syntax-aware token coloring
// ==============================================================================
//
// Walks all rnix syntax tokens and classifies each one using the Tix type
// information (name resolution, name kinds) for richer highlighting than
// plain TextMate grammars can provide.

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr, NameKind};
use rowan::ast::AstNode;
use tower_lsp::lsp_types::*;

use crate::state::FileAnalysis;

// ==============================================================================
// Legend: token types and modifiers
// ==============================================================================

const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::VARIABLE,  // 0
    SemanticTokenType::PARAMETER, // 1
    SemanticTokenType::PROPERTY,  // 2
    SemanticTokenType::FUNCTION,  // 3
    SemanticTokenType::KEYWORD,   // 4
    SemanticTokenType::STRING,    // 5
    SemanticTokenType::NUMBER,    // 6
    SemanticTokenType::COMMENT,   // 7
    SemanticTokenType::OPERATOR,  // 8
];

const TOKEN_MODIFIERS: &[SemanticTokenModifier] = &[
    SemanticTokenModifier::DEFINITION,      // bit 0
    SemanticTokenModifier::DEFAULT_LIBRARY, // bit 1
];

const MOD_DEFINITION: u32 = 1 << 0;
const MOD_DEFAULT_LIBRARY: u32 = 1 << 1;

pub fn legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: TOKEN_TYPES.to_vec(),
        token_modifiers: TOKEN_MODIFIERS.to_vec(),
    }
}

pub fn semantic_tokens(analysis: &FileAnalysis, root: &rnix::Root) -> Vec<SemanticToken> {
    let mut raw_tokens = Vec::new();

    // Walk all tokens in the syntax tree in source order.
    for token in root.syntax().descendants_with_tokens() {
        let token = match token.into_token() {
            Some(t) => t,
            None => continue,
        };

        let (token_type, token_modifiers) = match classify_token(analysis, root, &token) {
            Some(classification) => classification,
            None => continue,
        };

        let range = analysis.line_index.range(token.text_range());

        // For multi-line tokens the end character can be less than the start
        // character (it's on a different line), so use saturating subtraction
        // and fall back to the raw text length.
        let length = range
            .end
            .character
            .checked_sub(range.start.character)
            .unwrap_or(token.text_range().len().into());

        raw_tokens.push(RawToken {
            line: range.start.line,
            start: range.start.character,
            length,
            token_type,
            token_modifiers,
        });
    }

    // Delta-encode: each token's position is relative to the previous one.
    let mut result = Vec::with_capacity(raw_tokens.len());
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;

    for tok in &raw_tokens {
        let delta_line = tok.line - prev_line;
        let delta_start = if delta_line == 0 {
            tok.start - prev_start
        } else {
            tok.start
        };

        result.push(SemanticToken {
            delta_line,
            delta_start,
            length: tok.length,
            token_type: tok.token_type,
            token_modifiers_bitset: tok.token_modifiers,
        });

        prev_line = tok.line;
        prev_start = tok.start;
    }

    result
}

struct RawToken {
    line: u32,
    start: u32,
    length: u32,
    token_type: u32,
    token_modifiers: u32,
}

/// Classify a single syntax token. Returns (token_type_index, modifier_bitset)
/// or None if the token should be skipped (whitespace, delimiters, etc.).
fn classify_token(
    analysis: &FileAnalysis,
    root: &rnix::Root,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<(u32, u32)> {
    use rnix::SyntaxKind;

    match token.kind() {
        // Keywords.
        SyntaxKind::TOKEN_LET
        | SyntaxKind::TOKEN_IN
        | SyntaxKind::TOKEN_IF
        | SyntaxKind::TOKEN_THEN
        | SyntaxKind::TOKEN_ELSE
        | SyntaxKind::TOKEN_WITH
        | SyntaxKind::TOKEN_REC
        | SyntaxKind::TOKEN_INHERIT
        | SyntaxKind::TOKEN_ASSERT => Some((4, 0)),

        // Strings and paths.
        SyntaxKind::TOKEN_STRING_CONTENT
        | SyntaxKind::TOKEN_STRING_START
        | SyntaxKind::TOKEN_STRING_END
        | SyntaxKind::TOKEN_PATH
        | SyntaxKind::TOKEN_URI => Some((5, 0)),

        // Numbers.
        SyntaxKind::TOKEN_INTEGER | SyntaxKind::TOKEN_FLOAT => Some((6, 0)),

        // Comments.
        SyntaxKind::TOKEN_COMMENT => Some((7, 0)),

        // Operators.
        SyntaxKind::TOKEN_ADD
        | SyntaxKind::TOKEN_SUB
        | SyntaxKind::TOKEN_MUL
        | SyntaxKind::TOKEN_DIV
        | SyntaxKind::TOKEN_CONCAT
        | SyntaxKind::TOKEN_UPDATE
        | SyntaxKind::TOKEN_AND_AND
        | SyntaxKind::TOKEN_OR_OR
        | SyntaxKind::TOKEN_EQUAL
        | SyntaxKind::TOKEN_NOT_EQUAL
        | SyntaxKind::TOKEN_LESS
        | SyntaxKind::TOKEN_LESS_OR_EQ
        | SyntaxKind::TOKEN_MORE
        | SyntaxKind::TOKEN_MORE_OR_EQ
        | SyntaxKind::TOKEN_IMPLICATION
        | SyntaxKind::TOKEN_INVERT => Some((8, 0)),

        // Identifiers — classify using AST information.
        SyntaxKind::TOKEN_IDENT => classify_ident(analysis, root, token),

        _ => None,
    }
}

/// Classify an identifier token using the source map and name resolution.
fn classify_ident(
    analysis: &FileAnalysis,
    _root: &rnix::Root,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
) -> Option<(u32, u32)> {
    let text = token.text();

    // Keyword-like identifiers.
    match text {
        "true" | "false" | "null" => return Some((4, 0)),
        _ => {}
    }

    // Walk up from the token to find a source map entry.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Definition site: name node.
        if let Some(name_id) = analysis.source_map.name_for_node(ptr) {
            let kind = analysis.module[name_id].kind;
            let type_idx = name_kind_to_token_type(kind);
            return Some((type_idx, MOD_DEFINITION));
        }

        // Expression site.
        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            if matches!(&analysis.module[expr_id], Expr::Reference(_)) {
                if let Some(resolved) = analysis.name_res.get(expr_id) {
                    return Some(match resolved {
                        ResolveResult::Builtin(_) => (3, MOD_DEFAULT_LIBRARY),
                        ResolveResult::Definition(name_id) => {
                            let kind = analysis.module[*name_id].kind;
                            (name_kind_to_token_type(kind), 0)
                        }
                        ResolveResult::WithExprs(..) => (0, 0), // VARIABLE
                    });
                }
            }
            // Non-reference expression — stop walking.
            return None;
        }

        node = node.parent()?;
    }
}

/// Map a NameKind to a semantic token type index.
fn name_kind_to_token_type(kind: NameKind) -> u32 {
    match kind {
        NameKind::LetIn => 0,                               // VARIABLE
        NameKind::PlainAttrset | NameKind::RecAttrset => 2, // PROPERTY
        NameKind::Param => 1,                               // PARAMETER
        NameKind::PatField => 1,                            // PARAMETER
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::temp_path;
    use lang_check::aliases::TypeAliasRegistry;

    /// Get semantic tokens for a source string. Returns the raw tokens with
    /// absolute positions (not delta-encoded) for easier assertions.
    fn get_tokens(src: &str) -> Vec<(u32, u32, u32, u32, u32)> {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), src.to_string());
        let analysis = state.get_file(&path).unwrap();
        let root = rnix::Root::parse(src).tree();

        let tokens = semantic_tokens(analysis, &root);

        // Convert delta-encoded tokens back to absolute positions.
        let mut result = Vec::new();
        let mut line = 0u32;
        let mut start = 0u32;
        for tok in &tokens {
            line += tok.delta_line;
            if tok.delta_line > 0 {
                start = tok.delta_start;
            } else {
                start += tok.delta_start;
            }
            result.push((
                line,
                start,
                tok.length,
                tok.token_type,
                tok.token_modifiers_bitset,
            ));
        }
        result
    }

    #[test]
    fn let_in_basic() {
        let src = "let x = 1; in x";
        let tokens = get_tokens(src);

        // Find specific tokens by their text position.
        // "let" at (0,0) should be KEYWORD (4)
        assert!(
            tokens.iter().any(|t| t.0 == 0 && t.1 == 0 && t.3 == 4),
            "let should be KEYWORD: {tokens:?}"
        );
        // "x" at (0,4) should be VARIABLE+DEFINITION (0, mod 1)
        assert!(
            tokens
                .iter()
                .any(|t| t.0 == 0 && t.1 == 4 && t.3 == 0 && t.4 == MOD_DEFINITION),
            "x def should be VARIABLE+DEFINITION: {tokens:?}"
        );
        // "1" at (0,8) should be NUMBER (6)
        assert!(
            tokens.iter().any(|t| t.0 == 0 && t.1 == 8 && t.3 == 6),
            "1 should be NUMBER: {tokens:?}"
        );
        // "in" at (0,11) should be KEYWORD (4)
        assert!(
            tokens.iter().any(|t| t.0 == 0 && t.1 == 11 && t.3 == 4),
            "in should be KEYWORD: {tokens:?}"
        );
        // "x" at (0,14) should be VARIABLE (0, no mod)
        assert!(
            tokens
                .iter()
                .any(|t| t.0 == 0 && t.1 == 14 && t.3 == 0 && t.4 == 0),
            "x ref should be VARIABLE (no mod): {tokens:?}"
        );
    }

    #[test]
    fn keyword_literals() {
        let src = "[ true false null ]";
        let tokens = get_tokens(src);
        // All three should be KEYWORD (4).
        let keyword_count = tokens.iter().filter(|t| t.3 == 4).count();
        assert_eq!(
            keyword_count, 3,
            "true/false/null should be keywords: {tokens:?}"
        );
    }

    #[test]
    fn string_tokens() {
        let src = r#""hello""#;
        let tokens = get_tokens(src);
        // Should have STRING tokens (5).
        assert!(
            tokens.iter().any(|t| t.3 == 5),
            "string content should be STRING: {tokens:?}"
        );
    }

    #[test]
    fn attrset_field_is_property() {
        let src = "{ a = 1; }";
        let tokens = get_tokens(src);
        // "a" should be PROPERTY+DEFINITION (2, mod 1)
        assert!(
            tokens.iter().any(|t| t.3 == 2 && t.4 == MOD_DEFINITION),
            "attrset field should be PROPERTY+DEFINITION: {tokens:?}"
        );
    }

    #[test]
    fn lambda_param_is_parameter() {
        let src = "x: x";
        let tokens = get_tokens(src);
        // First "x" should be PARAMETER+DEFINITION (1, mod 1).
        assert!(
            tokens.iter().any(|t| t.3 == 1 && t.4 == MOD_DEFINITION),
            "lambda param should be PARAMETER+DEFINITION: {tokens:?}"
        );
        // Second "x" should be PARAMETER (1, mod 0).
        assert!(
            tokens.iter().any(|t| t.3 == 1 && t.4 == 0),
            "param reference should be PARAMETER: {tokens:?}"
        );
    }

    #[test]
    fn multiline_delta_encoding() {
        let src = "let\n  x = 1;\nin x";
        let tokens = get_tokens(src);
        // Verify there are tokens on different lines.
        let lines: Vec<u32> = tokens.iter().map(|t| t.0).collect();
        assert!(
            lines.iter().any(|&l| l > 0),
            "should have tokens on multiple lines: {lines:?}"
        );
    }

    #[test]
    fn multiline_string_no_overflow() {
        // Multi-line strings produce a token where end.character < start.character
        // (the end is on a later line with a smaller column). This must not panic
        // with a subtraction overflow.
        let src = "''\n  hello\n  world\n''";
        let tokens = get_tokens(src);
        // Should produce at least one STRING token (5) without panicking.
        assert!(
            tokens.iter().any(|t| t.3 == 5),
            "multiline string should produce STRING tokens: {tokens:?}"
        );
    }

    #[test]
    fn builtin_is_function_default_library() {
        let src = "import ./foo.nix";
        let tokens = get_tokens(src);
        // "import" should be FUNCTION+DEFAULT_LIBRARY (3, mod 2).
        assert!(
            tokens
                .iter()
                .any(|t| t.3 == 3 && t.4 == MOD_DEFAULT_LIBRARY),
            "import should be FUNCTION+DEFAULT_LIBRARY: {tokens:?}"
        );
    }
}
