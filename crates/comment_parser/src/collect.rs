use pest::iterators::Pairs;

use crate::{KnownTy, Rule, TypeDecl, TypeVarValue};

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
            _ => {
                unreachable!("Should be handle by type line: {:?}", pair.as_rule())
            }
        }
    }

    decls
}

pub fn collect_type_expr(mut pairs: Pairs<Rule>) -> Option<KnownTy> {
    let curr = pairs.next()?;

    let curr = match curr.as_rule() {
        Rule::type_expr
        | Rule::arrow_segment
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref => collect_type_expr(curr.into_inner()).unwrap(),
        Rule::list_type => KnownTy::List(collect_type_expr(curr.into_inner()).unwrap().into()),
        Rule::string_ref => KnownTy::Primitive(lang::PrimitiveTy::String),
        Rule::int_ref => KnownTy::Primitive(lang::PrimitiveTy::Int),
        Rule::bool_ref => KnownTy::Primitive(lang::PrimitiveTy::Bool),
        Rule::float_ref => KnownTy::Primitive(lang::PrimitiveTy::Float),
        Rule::path_ref => KnownTy::Primitive(lang::PrimitiveTy::Path),
        Rule::null_ref => KnownTy::Primitive(lang::PrimitiveTy::Null),
        Rule::generic_ident => KnownTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
        Rule::user_type => KnownTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
        Rule::other_text | Rule::EOI | Rule::WHITESPACE | Rule::NEWLINE | Rule::ANY_WHITESPACE => {
            unreachable!("should not be seen whitespace...")
        }
        _ => unreachable!("collect_type_expr should not be seen: {:?}", curr.as_rule()),
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
                },
            },
            TypeDecl {
                identifier: "compose".into(),
                type_expr: known_ty! {
                    ((# "b") -> (# "c")) -> ((# "a") -> (# "b")) -> (# "a") -> (# "c")
                },
            },
            TypeDecl {
                identifier: "const_var".into(),
                type_expr: known_ty! {
                    int
                },
            },
            TypeDecl {
                identifier: "const_lst".into(),
                type_expr: known_ty! {
                    [int]
                },
            },
        ];

        assert_eq!(decs, expected)
    }
}
