use rnix::ast::{self, HasEntry};
use smol_str::SmolStr;

pub fn flatten_paren(expr: ast::Expr) -> Option<ast::Expr> {
    let mut cur = Some(expr);
    while let Some(ast::Expr::Paren(p)) = cur {
        cur = p.expr();
    }
    cur
}

pub(super) fn name_of_ident(ident: &ast::Ident) -> Option<SmolStr> {
    ident.ident_token().map(|i| i.text().into())
}

pub(super) fn get_str_literal(s: &ast::Str) -> Option<String> {
    if s.parts()
        .any(|p| matches!(p, ast::InterpolPart::Interpolation(_)))
    {
        return None;
    }

    let parts = s.normalized_parts();

    if parts.len() > 1 {
        panic!(
            "There should only be at most one string part if there is no interpolation\n{s}\n parts:{}",
            parts.len()
        );
    }

    let lit = match parts.first() {
        Some(ast::InterpolPart::Literal(lit)) => lit,
        _ => "", // if not parts its an empty string
    };

    Some(lit.to_string())
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AttrKind {
    Static(Option<SmolStr>),
    Dynamic(Option<rnix::ast::Expr>),
}

impl AttrKind {
    /// Classify the dynamic-ness of an `Attr`, by
    /// unwrapping nested parentheses and extracting string literals.
    pub fn of(attr: rnix::ast::Attr) -> Self {
        let s = match attr {
            rnix::ast::Attr::Ident(ident) => return Self::Static(name_of_ident(&ident)),
            rnix::ast::Attr::Str(s) => s,
            rnix::ast::Attr::Dynamic(d) => match d.expr().and_then(flatten_paren) {
                Some(rnix::ast::Expr::Str(s)) => s,
                e => return Self::Dynamic(e),
            },
        };

        match get_str_literal(&s) {
            Some(lit) => Self::Static(Some(lit.into())),
            None => Self::Dynamic(Some(rnix::ast::Expr::Str(s))),
        }
    }
}
