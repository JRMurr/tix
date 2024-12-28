use rnix::ast::{HasEntry, Ident};
use std::collections::HashMap;

use id_arena::{Arena, Id};

pub type ExprId = Id<Expr>;

#[derive(Debug, PartialEq)]
pub enum Literal {
    Float(f64),
    Integer(i64),
    Uri, // TODO:
}

type Param = String; // TODO: real type

#[derive(Debug, PartialEq)]
pub enum Expr {
    Apply {
        fun: ExprId,
        args: ExprId, // TODO should args be a vec of exprs?
    },
    Str(String),  // TODO: handle interpolation
    Path(String), // TODO: handle interpolation
    Literal(Literal),
    Func {
        params: Param,
        body: ExprId,
    },
    LetIn {
        bindings: Vec<ExprId>, // TODO: should we include the keys/attrpaths here or would the scope info hold that?
        body: ExprId,
    },
    List(Vec<ExprId>),
    BinOp {
        lhs: ExprId,
        rhs: ExprId,
        op: rnix::ast::BinOpKind,
    },
    Paren(ExprId),
    AttrSet {
        is_rec: bool,
        entries: Vec<ExprId>, // TODO: should we include the keys/attrpaths here or would the scope info hold that?
    },
    UnaryOp {
        op: rnix::ast::UnaryOpKind,
        expr: ExprId,
    },
    Identifier(String),
    // not mapped yet
    // Select
    // Error
    // Assert
    // With
    // HasAttr

    // not sure if needed
    // Root
}

// TODO: real type;
pub type SymbolType = String;

#[derive(Debug)]
pub struct Symbol {
    // TODO: maybe yeet and just have span and type here
    // since the scope has the name in the key?
    name: String,
    // TODO: span info
    ty: SymbolType,
}

impl Symbol {
    pub fn new(name: String, ty: SymbolType) -> Self {
        Self { name, ty }
    }
}

pub type ScopeId = Id<Scope>;
// pub type SymbolID = Id<Symbol>;

#[derive(Debug)]
pub struct Scope {
    // TODO: might be good to make this symbol id as the value during type resolution for easy changes
    // would make lookup slightly more annoying though since we would need the arena
    symbols: HashMap<String, Symbol>,
    parent: Option<ScopeId>,
}

impl Scope {
    pub fn new(parent: Option<ScopeId>) -> Self {
        Self {
            symbols: HashMap::new(),
            parent,
        }
    }

    pub fn get_symbol(&self, name: &String) -> Option<&Symbol> {
        self.symbols.get(name)
    }
}

#[derive(Debug)]
pub struct ExprTable {
    scopes: Arena<Scope>,
    // symbols: Arena<Symbol>,
    expressions: Arena<Expr>,
    scope_lookup: HashMap<ExprId, ScopeId>, // might be nice to make a special arena map like https://docs.rs/la-arena/0.3.1/la_arena/struct.ArenaMap.html
}

impl ExprTable {
    pub fn new() -> Self {
        Self {
            scopes: Arena::new(),
            // symbols: Arena::new(),
            expressions: Arena::new(),
            scope_lookup: HashMap::new(),
        }
    }

    pub fn add_expr(&mut self, expr: Expr) -> ExprId {
        // TODO: error if expr alredy in or return back the same id?
        self.expressions.alloc(expr)
    }

    pub fn add_scope(&mut self, scope: Scope) -> ScopeId {
        self.scopes.alloc(scope)
    }

    pub fn add_symbol(&mut self, scope_id: ScopeId, symbol: Symbol) {
        // TODO: error if adding the same symbol to the scope (could do name equality)
        let scope = self
            .scopes
            .get_mut(scope_id)
            .expect("Scope with id {scope_id} not found");

        // let symbol_id = self.symbols.alloc(symbol);

        let name = symbol.name.clone();

        scope.symbols.insert(name, symbol);

        // symbol_id
    }

    pub fn get_symbol(&self, scope_id: ScopeId, name: String) -> Option<&Symbol> {
        let mut curr_scope = self.scopes.get(scope_id);

        while let Some(scope) = curr_scope {
            let symbol = scope.get_symbol(&name);

            if symbol.is_some() {
                return symbol;
            }

            curr_scope = scope.parent.and_then(|p| self.scopes.get(p));
        }

        None
    }

    pub fn get_expr(&self, expr_id: ExprId) -> &Expr {
        &self.expressions[expr_id]
    }

    pub fn transform_ast(&mut self, rnix_expr: rnix::ast::Expr, parent: Option<ScopeId>) -> ExprId {
        use rnix::ast;

        let scope_id = self.add_scope(Scope::new(parent));

        let expr: Expr = match rnix_expr {
            ast::Expr::Apply(apply) => {
                let fun = apply.lambda().expect("Should have function to apply to");
                let fun = self.transform_ast(fun, Some(scope_id));

                let args = apply
                    .argument()
                    .expect("Should have arguments to apply to function");
                let args = self.transform_ast(args, Some(scope_id));

                Expr::Apply { fun, args }
            }

            ast::Expr::IfElse(if_else) => todo!(),
            ast::Expr::Select(select) => todo!(),
            ast::Expr::Str(_nix_str) => {
                // TODO: real handling
                Expr::Str("TODO!".to_string())
            }
            ast::Expr::Path(path) => {
                // TODO: real handling
                Expr::Path("TODO!".to_string())
            }
            ast::Expr::Literal(literal) => {
                let lit = match literal.kind() {
                    ast::LiteralKind::Float(float) => {
                        Literal::Float(float.value().expect("should be valid float"))
                    }
                    ast::LiteralKind::Integer(integer) => {
                        Literal::Integer(integer.value().expect("should be valid integer"))
                    }
                    ast::LiteralKind::Uri(uri) => Literal::Uri,
                };

                Expr::Literal(lit)
            }
            ast::Expr::Lambda(lambda) => {
                let params = lambda.param().expect("Should have lambda params");

                match params {
                    ast::Param::Pattern(p) => {
                        // TODO: handle
                        eprintln!("TODO: need to handle pattern params {p}")
                    }
                    ast::Param::IdentParam(ident_param) => {
                        let ident = ident_param
                            .ident()
                            .expect("ident_param should have an ident...");
                        let name = name_of_ident(&ident);

                        self.add_symbol(
                            scope_id,
                            Symbol::new(name.to_string(), "TODO: TYPE".to_string()),
                        );
                    }
                }

                let body = lambda.body().expect("Should have lambda body");

                let body = self.transform_ast(body, Some(scope_id));

                Expr::Func {
                    params: "TODO: REAL PARAMS".to_string(),
                    body,
                }
            }
            ast::Expr::LetIn(let_in) => {
                let bindings: Vec<ExprId> = let_in
                    .entries()
                    .map(|entry| match entry {
                        rnix::ast::Entry::Inherit(inherit) => {
                            todo!("inherit is not handled in let in: {inherit}");
                        }
                        rnix::ast::Entry::AttrpathValue(attrpath_value) => {
                            dbg!(attrpath_value.to_string());

                            // TODO: handle the actual vars under
                            // attrpath_value.attrpath()
                            // add them to the scope

                            let value = attrpath_value
                                .value()
                                .expect("Should have a value for the binding");

                            self.transform_ast(value, Some(scope_id))
                        }
                    })
                    .collect();

                let body = let_in.body().expect("Should have a let in body");

                let body = self.transform_ast(body, Some(scope_id));

                Expr::LetIn { bindings, body }
            }
            ast::Expr::List(list) => todo!(),
            ast::Expr::BinOp(bin_op) => {
                let lhs = bin_op.lhs().expect("Should have lhs");
                let lhs = self.transform_ast(lhs, Some(scope_id));

                let op = bin_op.operator().expect("Should have operator");

                let rhs = bin_op.rhs().expect("Should have rhs");
                let rhs = self.transform_ast(rhs, Some(scope_id));

                Expr::BinOp { lhs, rhs, op }
            }
            ast::Expr::Paren(paren) => Expr::Paren(self.transform_ast(
                paren.expr().expect("Should have inner expr"),
                Some(scope_id),
            )),
            ast::Expr::AttrSet(attr_set) => {
                // TODO: only symbols if the attr_set is rec
                let mut attrpaths: Vec<ExprId> = attr_set
                    .attrpath_values()
                    .map(|attrpath_value| {
                        dbg!(attrpath_value.to_string());

                        let attr_path = attrpath_value.attrpath().expect("Should have attrpath");

                        // TODO: make this loop a helper somehow, dupe with below
                        for attr in attr_path.attrs() {
                            match attr {
                                ast::Attr::Ident(ident) => {
                                    let name = name_of_ident(&ident);
                                    self.add_symbol(
                                        scope_id,
                                        Symbol::new(name, "TODO: TYPE".to_string()),
                                    )
                                }
                                ast::Attr::Dynamic(_dynamic) => todo!(),
                                ast::Attr::Str(_) => todo!(),
                            }
                        }

                        let value = attrpath_value
                            .value()
                            .expect("Should have a value for the binding");

                        self.transform_ast(value, Some(scope_id))
                    })
                    .collect();

                let inherits: Vec<ExprId> = attr_set
                    .inherits()
                    .flat_map(|inherit| {
                        if let Some(_from) = inherit.from() {
                            todo!("inherting from a var is not supported yet");
                        }
                        for attr in inherit.attrs() {
                            match attr {
                                ast::Attr::Ident(ident) => {
                                    let name = name_of_ident(&ident);
                                    self.add_symbol(
                                        scope_id,
                                        Symbol::new(name, "TODO: TYPE".to_string()),
                                    )
                                }
                                ast::Attr::Dynamic(_dynamic) => todo!(),
                                ast::Attr::Str(_) => todo!(),
                            }
                        }

                        None
                    })
                    .collect();

                attrpaths.extend(inherits);

                Expr::AttrSet {
                    is_rec: attr_set.rec_token().is_some(),
                    entries: attrpaths,
                }
            }
            ast::Expr::UnaryOp(unary_op) => todo!(),
            ast::Expr::Ident(ident) => Expr::Identifier(name_of_ident(&ident)),

            ast::Expr::Assert(assert) => todo!(),
            ast::Expr::Error(error) => todo!(),
            ast::Expr::With(with) => todo!(),
            ast::Expr::HasAttr(has_attr) => todo!(),

            ast::Expr::Root(_root) => todo!(),
            ast::Expr::LegacyLet(_legacy_let) => todo!(),
        };

        let expr_id = self.add_expr(expr);

        self.scope_lookup.insert(expr_id, scope_id);

        expr_id
    }

    fn handle_entries(&mut self, node: impl rnix::ast::HasEntry, scope_id: ScopeId) {}
}

fn name_of_ident(ident: &Ident) -> String {
    let ident_token = ident.ident_token().expect("Should have ident token");
    ident_token.text().to_string()
}

// fn convert_to_expr(root: rnix::ast::Expr, )
