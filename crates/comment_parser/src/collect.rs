use pest::iterators::Pairs;

use crate::{KnownTy, Rule, TypeDecl};

pub fn collect_type_decls(pairs: Pairs<Rule>) -> Vec<TypeDecl> {
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
                // let expr_rule = inner.next().unwrap(); // type_expr

                decls.push(TypeDecl {
                    identifier: ident_rule.as_str().into(),
                    type_expr: collect_type_expr(inner).unwrap(),
                });
            }
            Rule::comment_content => {
                decls.extend(collect_type_decls(pair.into_inner()));
            }
            Rule::other_text
            | Rule::EOI
            | Rule::WHITESPACE
            | Rule::NEWLINE
            | Rule::ANY_WHITESPACE => {}
            Rule::arrow_segment
            | Rule::type_expr
            | Rule::identifier
            | Rule::paren_type
            | Rule::list_type
            | Rule::simple_type => {
                unreachable!("Should be handle by type line")
            }
        }
    }

    decls
}

pub fn collect_type_expr(mut pairs: Pairs<Rule>) -> Option<KnownTy> {
    let curr = pairs.next()?;

    let curr = match curr.as_rule() {
        // wrapper rules (show this be shallow?)
        Rule::type_expr | Rule::arrow_segment | Rule::paren_type => {
            collect_type_expr(curr.into_inner()).unwrap()
        }
        Rule::list_type => KnownTy::List(collect_type_expr(curr.into_inner()).unwrap().into()),
        Rule::simple_type => KnownTy::TyVar(curr.as_str().into()),
        Rule::other_text | Rule::EOI | Rule::WHITESPACE | Rule::NEWLINE | Rule::ANY_WHITESPACE => {
            unreachable!("should not be seen whitespace...")
        }
        _ => unreachable!("should not be seen"),
    };

    // if theres more than this expression is the argument to a lambda
    if let Some(lam_body) = collect_type_expr(pairs) {
        return Some(KnownTy::Lambda {
            param: curr.into(),
            body: lam_body.into(),
        });
    }

    Some(curr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{known_ty, parse_comment_text};

    #[test]
    fn it_works() {
        let example_comment = r#"
        This is some text
        type:
        ```
        mapMe :: [a] -> (a -> b) -> [b]
        compose :: (b -> c) -> (a -> b) -> a -> c
        const_var :: int
        const_lst :: [ int ]
        ```
        Some more doc lines
    "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![
            TypeDecl {
                identifier: "mapMe".into(),
                type_expr: known_ty! {
                    [(# "a")] -> ((# "a") -> (# "b")) -> [(# "b")]
                }, //"[a] -> (a -> b) -> [b]".to_string(),
            },
            TypeDecl {
                identifier: "compose".into(),
                type_expr: known_ty! {
                    ((# "b") -> (# "c")) -> ((# "a") -> (# "b")) -> (# "a") -> (# "c")
                }, //"(b -> c) -> (a -> b) -> a -> c".to_string(),
            },
            TypeDecl {
                identifier: "const_var".into(),
                type_expr: known_ty! {
                    (# "int") // todo: real int type not ty var
                }, //"int".to_string(),
            },
            TypeDecl {
                identifier: "const_lst".into(),
                type_expr: known_ty! {
                    [(# "int")] // todo: real int type not ty var
                }, // "[ int ]".to_string(),
            },
        ];

        assert_eq!(decs, expected)
    }
}
