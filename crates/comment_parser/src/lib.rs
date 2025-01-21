use pest::{Parser, iterators::Pairs};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "comment.pest"]
pub struct CommentParser;

// box the error since rust warning about error type being too big
// TODO: is this normal for pest or is my grammar bad...
type ParseError = Box<pest::error::Error<Rule>>;

pub fn parse_comment_text(source: &str) -> Result<Pairs<Rule>, ParseError> {
    Ok(CommentParser::parse(Rule::comment_content, source)?)
}

#[derive(Debug, PartialEq, Eq)]
pub struct HaskellTypeDecl {
    pub identifier: String,
    pub type_expr: String,
}

pub fn collect_type_decls(pairs: Pairs<Rule>) -> Vec<HaskellTypeDecl> {
    let mut decls = Vec::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::type_block | Rule::block_content => {
                // Descend into children to find type_line
                decls.extend(collect_type_decls(pair.into_inner()));
            }
            Rule::type_line => {
                let mut inner = pair.into_inner();
                let ident_rule = inner.next().unwrap(); // identifier
                let expr_rule = inner.next().unwrap(); // type_expr

                decls.push(HaskellTypeDecl {
                    identifier: ident_rule.as_str().to_string(),
                    type_expr: expr_rule.as_str().to_string(),
                });
            }
            // Recurse or skip other rules as needed
            Rule::comment_content | Rule::arrow_segment | Rule::type_expr => {
                decls.extend(collect_type_decls(pair.into_inner()));
            }
            _ => {}
        }
    }

    decls
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let example_comment = r#"
        This is some text
        type:
        ```
        mapMe :: [a] -> (a -> b) -> [b]
        compose :: (b -> c) -> (a -> b) -> a -> c
        const_var :: int
        ```
        Some more doc lines
    "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![
            HaskellTypeDecl {
                identifier: "mapMe".to_string(),
                type_expr: "[a] -> (a -> b) -> [b]".to_string(),
            },
            HaskellTypeDecl {
                identifier: "compose".to_string(),
                type_expr: "(b -> c) -> (a -> b) -> a -> c".to_string(),
            },
            HaskellTypeDecl {
                identifier: "const_var".to_string(),
                type_expr: "int".to_string(),
            },
        ];

        assert_eq!(decs, expected)
    }
}
