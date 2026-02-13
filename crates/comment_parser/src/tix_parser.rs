use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "tix_decl.pest"]
pub struct TixDeclParser;
