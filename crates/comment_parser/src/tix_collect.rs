// ==============================================================================
// .tix declaration file collection
// ==============================================================================
//
// Walks the pest parse tree from `tix_decl.pest` and produces structured
// `TixDeclFile` / `TixDeclaration` values. Type expression collection mirrors
// `collect.rs` but uses `tix_parser::Rule` variants.

use lang_ty::{AttrSetTy, PrimitiveTy};
use pest::iterators::Pairs;
use smol_str::SmolStr;
use std::collections::BTreeMap;

use crate::tix_parser::Rule;
use crate::{ParsedTy, ParsedTyRef, TixDeclFile, TixDeclaration, TypeVarValue};

pub fn collect_tix_file(pairs: Pairs<Rule>) -> TixDeclFile {
    let mut declarations = Vec::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::tix_file => {
                return collect_tix_file(pair.into_inner());
            }
            Rule::type_alias_decl => {
                let mut inner = pair.into_inner();
                let name: SmolStr = inner.next().unwrap().as_str().into();
                let body = collect_type_expr(inner).unwrap();
                declarations.push(TixDeclaration::TypeAlias { name, body });
            }
            Rule::val_decl => {
                let mut inner = pair.into_inner();
                let name: SmolStr = inner.next().unwrap().as_str().into();
                let ty = collect_type_expr(inner).unwrap();
                declarations.push(TixDeclaration::ValDecl { name, ty });
            }
            Rule::module_decl => {
                let mut inner = pair.into_inner();
                let name: SmolStr = inner.next().unwrap().as_str().into();
                // Remaining children are the nested declarations.
                let nested = collect_declarations(inner);
                declarations.push(TixDeclaration::Module {
                    name,
                    declarations: nested,
                });
            }
            Rule::EOI => {}
            _ => unreachable!("collect_tix_file: unexpected rule {:?}", pair.as_rule()),
        }
    }

    TixDeclFile { declarations }
}

fn collect_declarations(pairs: Pairs<Rule>) -> Vec<TixDeclaration> {
    let file = collect_tix_file(pairs);
    file.declarations
}

// =============================================================================
// Type expression collection — mirrors collect.rs but for tix_parser::Rule
// =============================================================================

fn collect_type_expr(mut pairs: Pairs<Rule>) -> Option<ParsedTy> {
    let curr = pairs.next()?;

    let curr = match curr.as_rule() {
        // Transparent wrappers.
        Rule::type_expr
        | Rule::arrow_segment
        | Rule::paren_type
        | Rule::type_ref
        | Rule::primitive_ref
        | Rule::atom_type => collect_type_expr(curr.into_inner()).unwrap(),

        Rule::union_type => collect_union(curr.into_inner()),
        Rule::isect_type => collect_intersection(curr.into_inner()),

        Rule::attrset_type => collect_attrset(curr.into_inner()),
        Rule::list_type => ParsedTy::List(collect_type_expr(curr.into_inner()).unwrap().into()),
        Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
        Rule::number_ref => ParsedTy::Primitive(PrimitiveTy::Number),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
        Rule::EOI => return None,
        _ => unreachable!(
            "tix collect_type_expr: unexpected rule {:?}",
            curr.as_rule()
        ),
    };

    // Arrow chaining: right-associative lambdas.
    if let Some(lam_body) = collect_type_expr(pairs) {
        return Some(ParsedTy::Lambda {
            param: curr.into(),
            body: lam_body.into(),
        });
    }

    Some(curr)
}

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
        Rule::number_ref => ParsedTy::Primitive(PrimitiveTy::Number),
        Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
        Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
        Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
        Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
        Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
        Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(pair.as_str().into())),
        Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(pair.as_str().into())),
        _ => unreachable!("tix collect_one: unexpected rule {:?}", pair.as_rule()),
    }
}

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
                let ty = collect_type_expr(inner).unwrap();
                dyn_ty = Some(ty.into());
            }
            Rule::open_marker => {
                open = true;
            }
            _ => unreachable!("tix collect_attrset: unexpected rule {:?}", pair.as_rule()),
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
    use crate::{known_ty, parse_tix_file};

    #[test]
    fn type_alias() {
        let file = parse_tix_file("type Derivation = { name: string, system: string };")
            .expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, body } => {
                assert_eq!(name.as_str(), "Derivation");
                assert_eq!(*body, known_ty!({ "name": string, "system": string }));
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }

    #[test]
    fn val_decl() {
        let file = parse_tix_file("val mkDerivation :: { name: string, ... } -> { name: string };")
            .expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, ty } => {
                assert_eq!(name.as_str(), "mkDerivation");
                assert_eq!(
                    *ty,
                    known_ty!(({ "name": string; ... }) -> ({ "name": string }))
                );
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn module_decl() {
        let src = r#"
            module lib {
                val id :: a -> a;
                module strings {
                    val concatStringsSep :: string -> [string] -> string;
                }
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::Module { name, declarations } => {
                assert_eq!(name.as_str(), "lib");
                assert_eq!(declarations.len(), 2);

                // First: val id
                match &declarations[0] {
                    crate::TixDeclaration::ValDecl { name, ty } => {
                        assert_eq!(name.as_str(), "id");
                        assert_eq!(*ty, known_ty!((# "a") -> (# "a")));
                    }
                    other => panic!("expected ValDecl, got: {other:?}"),
                }

                // Second: nested module
                match &declarations[1] {
                    crate::TixDeclaration::Module { name, declarations } => {
                        assert_eq!(name.as_str(), "strings");
                        assert_eq!(declarations.len(), 1);
                    }
                    other => panic!("expected Module, got: {other:?}"),
                }
            }
            other => panic!("expected Module, got: {other:?}"),
        }
    }

    #[test]
    fn combined_file() {
        let src = r#"
            # A type alias
            type Nullable = a | null;

            # A val declaration
            val mkDerivation :: { name: string, ... } -> { name: string };

            # A module
            module lib {
                val id :: a -> a;
            }
        "#;
        let file = parse_tix_file(src).expect("parse error");
        assert_eq!(file.declarations.len(), 3);
    }

    #[test]
    fn number_primitive_in_val() {
        let file = parse_tix_file("val add :: number -> number -> number;").expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::ValDecl { name, ty } => {
                assert_eq!(name.as_str(), "add");
                assert_eq!(*ty, known_ty!(number -> number -> number));
            }
            other => panic!("expected ValDecl, got: {other:?}"),
        }
    }

    #[test]
    fn generic_type_alias() {
        let file = parse_tix_file("type Nullable = a | null;").expect("parse error");

        assert_eq!(file.declarations.len(), 1);
        match &file.declarations[0] {
            crate::TixDeclaration::TypeAlias { name, body } => {
                assert_eq!(name.as_str(), "Nullable");
                assert_eq!(*body, known_ty!(union!((# "a"), null)));
            }
            other => panic!("expected TypeAlias, got: {other:?}"),
        }
    }
}
