use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "tix_decl.pest"]
#[grammar = "type_expr.pest"]
pub struct TixDeclParser;
