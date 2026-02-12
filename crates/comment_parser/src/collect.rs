use lang_ty::PrimitiveTy;
use pest::iterators::Pairs;

use crate::{ParsedTy, ParsedTyRef, Rule, TypeDecl, TypeVarValue};

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

pub fn collect_type_expr(mut pairs: Pairs<Rule>) -> Option<ParsedTy> {
    let curr = pairs.next()?;

    let curr = match curr.as_rule() {
        // Transparent wrappers — descend into their single child.
        Rule::type_expr | Rule::arrow_segment | Rule::paren_type | Rule::type_ref
        | Rule::primitive_ref | Rule::atom_type => {
            collect_type_expr(curr.into_inner()).unwrap()
        }

        // Union type: `isect_type ("|" isect_type)*`
        // If only one member, unwrap to avoid a spurious Union wrapper.
        Rule::union_type => collect_union(curr.into_inner()),

        // Intersection type: `atom_type ("&" atom_type)*`
        Rule::isect_type => collect_intersection(curr.into_inner()),

        Rule::list_type => {
            ParsedTy::List(collect_type_expr(curr.into_inner()).unwrap().into())
        }
        Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
        Rule::other_text | Rule::EOI | Rule::WHITESPACE | Rule::NEWLINE | Rule::ANY_WHITESPACE => {
            unreachable!("should not be seen whitespace...")
        }
        _ => unreachable!("collect_type_expr should not be seen: {:?}", curr.as_rule()),
    };

    // If there are more segments, this expression is the argument to a lambda.
    // `arrow_segment -> arrow_segment -> ...` builds right-associative Lambdas.
    if let Some(lam_body) = collect_type_expr(pairs) {
        return Some(ParsedTy::Lambda {
            param: curr.into(),
            body: lam_body.into(),
        });
    }

    Some(curr)
}

/// Collect a single type from a Pair. Dispatches on the pair's rule and
/// processes its children. Unlike `collect_type_expr`, this does NOT treat
/// remaining items as lambda body — it processes exactly one rule node.
fn collect_one(pair: pest::iterators::Pair<Rule>) -> ParsedTy {
    match pair.as_rule() {
        Rule::isect_type => collect_intersection(pair.into_inner()),
        Rule::atom_type | Rule::paren_type | Rule::type_ref | Rule::primitive_ref
        | Rule::arrow_segment | Rule::union_type | Rule::type_expr => {
            collect_type_expr(pair.into_inner()).unwrap()
        }
        Rule::list_type => ParsedTy::List(collect_type_expr(pair.into_inner()).unwrap().into()),
        Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(pair.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(pair.as_str().into())),
        _ => unreachable!("collect_one: unexpected rule {:?}", pair.as_rule()),
    }
}

/// Collect a union type from its children: `isect_type ("|" isect_type)*`.
/// If only one member, returns it directly (no spurious Union wrapper).
fn collect_union(pairs: Pairs<Rule>) -> ParsedTy {
    let members: Vec<ParsedTyRef> = pairs
        .map(|p| ParsedTyRef::from(collect_one(p)))
        .collect();

    match members.len() {
        0 => unreachable!("union_type must have at least one member"),
        1 => {
            let single = members.into_iter().next().unwrap();
            (*single.0).clone()
        }
        _ => ParsedTy::Union(members),
    }
}

/// Collect an intersection type from its children: `atom_type ("&" atom_type)*`.
/// If only one member, returns it directly.
fn collect_intersection(pairs: Pairs<Rule>) -> ParsedTy {
    let members: Vec<ParsedTyRef> = pairs
        .map(|p| ParsedTyRef::from(collect_one(p)))
        .collect();

    match members.len() {
        0 => unreachable!("isect_type must have at least one member"),
        1 => {
            let single = members.into_iter().next().unwrap();
            (*single.0).clone()
        }
        _ => ParsedTy::Intersection(members),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{known_ty, parse_comment_text};

    #[test]
    fn big_doc_comment() {
        let example_comment = r#"
        This is some text
        type:
        ```
        mapMe :: [a] -> (a -> b) -> [b]
        compose :: (b -> c) -> (a -> b) -> a -> c
        const_var :: int
        const_lst :: [ string ]
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
                    [string]
                },
            },
        ];

        assert_eq!(decs, expected)
    }

    #[test]
    fn simple() {
        let example_comment = r#"
            type: foo :: int -> int
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "foo".into(),
            type_expr: known_ty! {
                int -> int
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn union_type() {
        let example_comment = r#"
            type: flexible :: int | string | null
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "flexible".into(),
            type_expr: known_ty! {
                union!(int, string, null)
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn intersection_type() {
        let example_comment = r#"
            type: combined :: a & b
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "combined".into(),
            type_expr: known_ty! {
                isect!((# "a"), (# "b"))
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn union_in_arrow() {
        let example_comment = r#"
            type: process :: int | string -> bool
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        // `int | string -> bool` should parse as `(int | string) -> bool`
        // because `|` binds tighter than `->`.
        let expected = vec![TypeDecl {
            identifier: "process".into(),
            type_expr: known_ty! {
                (union!(int, string)) -> bool
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn intersection_binds_tighter_than_union() {
        let example_comment = r#"
            type: mixed :: int & bool | string
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        // `int & bool | string` should parse as `(int & bool) | string`
        // because `&` binds tighter than `|`.
        let expected = vec![TypeDecl {
            identifier: "mixed".into(),
            type_expr: known_ty! {
                union!((isect!(int, bool)), string)
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn parenthesized_union_in_lambda() {
        let example_comment = r#"
            type: f :: (int -> int) | (string -> string)
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");

        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "f".into(),
            type_expr: known_ty! {
                union!((int -> int), (string -> string))
            },
        }];

        assert_eq!(decs, expected)
    }
}
