use lang_ty::{AttrSetTy, PrimitiveTy};
use pest::iterators::Pairs;
use smol_str::SmolStr;
use std::collections::BTreeMap;

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
        // EOI can appear as a child of type_line when the doc comment text
        // ends without a trailing newline (the grammar's `(NEWLINE | EOI)`
        // terminator). It's not a type expression — return None.
        Rule::EOI => return None,

        // Transparent wrappers — descend into their single child.
        Rule::type_expr
        | Rule::arrow_segment
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref
        | Rule::atom_type => collect_type_expr(curr.into_inner()).unwrap(),

        // Union type: `isect_type ("|" isect_type)*`
        // If only one member, unwrap to avoid a spurious Union wrapper.
        Rule::union_type => collect_union(curr.into_inner()),

        // Intersection type: `atom_type ("&" atom_type)*`
        Rule::isect_type => collect_intersection(curr.into_inner()),

        Rule::attrset_type => collect_attrset(curr.into_inner()),
        Rule::list_type => ParsedTy::List(collect_type_expr(curr.into_inner()).unwrap().into()),
        Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
        Rule::other_text | Rule::WHITESPACE | Rule::NEWLINE | Rule::ANY_WHITESPACE => {
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
        Rule::atom_type
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref
        | Rule::arrow_segment
        | Rule::union_type
        | Rule::type_expr => collect_type_expr(pair.into_inner()).unwrap(),
        Rule::attrset_type => collect_attrset(pair.into_inner()),
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
    let members: Vec<ParsedTyRef> = pairs.map(|p| ParsedTyRef::from(collect_one(p))).collect();

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
    let members: Vec<ParsedTyRef> = pairs.map(|p| ParsedTyRef::from(collect_one(p))).collect();

    match members.len() {
        0 => unreachable!("isect_type must have at least one member"),
        1 => {
            let single = members.into_iter().next().unwrap();
            (*single.0).clone()
        }
        _ => ParsedTy::Intersection(members),
    }
}

/// Collect an attrset type from its children: `named_field*`, optional `dyn_field`,
/// optional `open_marker`.
fn collect_attrset(pairs: Pairs<Rule>) -> ParsedTy {
    let mut fields: BTreeMap<SmolStr, ParsedTyRef> = BTreeMap::new();
    let mut dyn_ty: Option<ParsedTyRef> = None;
    let mut open = false;

    for pair in pairs {
        match pair.as_rule() {
            Rule::named_field => {
                let mut inner = pair.into_inner();
                let name: SmolStr = inner.next().unwrap().as_str().into();
                let ty = collect_type_expr(inner).unwrap();
                fields.insert(name, ty.into());
            }
            Rule::dyn_field => {
                let inner = pair.into_inner();
                // The "_" token is consumed by the grammar rule; the inner
                // pairs contain only the type_expr.
                let ty = collect_type_expr(inner).unwrap();
                dyn_ty = Some(ty.into());
            }
            Rule::open_marker => {
                open = true;
            }
            _ => unreachable!("collect_attrset: unexpected rule {:?}", pair.as_rule()),
        }
    }

    ParsedTy::AttrSet(AttrSetTy {
        fields,
        dyn_ty,
        open,
    })
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
    fn attrset_closed() {
        let example_comment = r#"
            type: opts :: { name: string, age: int }
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");
        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "opts".into(),
            type_expr: known_ty! {
                { "name": string, "age": int }
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn attrset_open() {
        let example_comment = r#"
            type: opts :: { name: string, ... }
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");
        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "opts".into(),
            type_expr: known_ty! {
                { "name": string; ... }
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn attrset_dyn_field() {
        let example_comment = r#"
            type: dict :: { _: string }
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");
        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "dict".into(),
            type_expr: known_ty! {
                dyn_attrset!(string)
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn attrset_in_arrow() {
        let example_comment = r#"
            type: mkUser :: { name: string } -> int
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");
        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "mkUser".into(),
            type_expr: known_ty! {
                ({ "name": string }) -> int
            },
        }];

        assert_eq!(decs, expected)
    }

    #[test]
    fn attrset_only_open() {
        let example_comment = r#"
            type: any :: { ... }
        "#;
        let pairs = parse_comment_text(example_comment).expect("No parse error");
        let decs = collect_type_decls(pairs);

        let expected = vec![TypeDecl {
            identifier: "any".into(),
            type_expr: known_ty! {
                { ; ... }
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
