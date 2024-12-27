use id_arena::{Arena, Id};

// TODO: real type;
pub type SymbolType = String;

#[derive(Debug)]
pub struct Symbol {
    name: String, // TODO: maybe make this a CoW to save space?
    // TODO: span info
    ty: SymbolType,
}

impl Symbol {
    pub fn new(name: String, ty: SymbolType) -> Self {
        Self { name, ty }
    }
}

pub type ScopeId = Id<Scope>;
pub type SymbolID = Id<Symbol>;

#[derive(Debug)]
pub struct Scope {
    // TODO: should we hold the expression contains this scope here?
    symbols: Vec<SymbolID>,
    parent: Option<ScopeId>, // Reference to the parent scope
}

impl Scope {
    pub fn new(parent: Option<ScopeId>) -> Self {
        Self {
            symbols: Vec::new(),
            parent,
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    scopes: Arena<Scope>,
    symbols: Arena<Symbol>,
    // TODO: does it make sense to track the "root"/global scope here?
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            scopes: Arena::new(),
            symbols: Arena::new(),
        }
    }

    pub fn new_scope(&mut self, current_scope: Option<ScopeId>) -> ScopeId {
        let scope = Scope::new(current_scope);
        self.scopes.alloc(scope)
    }

    pub fn add_symbol(&mut self, scope_id: ScopeId, symbol: Symbol) -> SymbolID {
        let scope = self
            .scopes
            .get_mut(scope_id)
            .expect("Scope with id {scope_id} not found");

        let symbol_id = self.symbols.alloc(symbol);

        scope.symbols.push(symbol_id);

        symbol_id
    }
}
