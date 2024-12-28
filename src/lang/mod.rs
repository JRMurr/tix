// A lot of the code in this module is based on
// https://github.com/oxalica/nil/tree/main/crates/ide/src/def

// pub mod expr_table;
pub mod lower;

mod ast_utils;

use std::{collections::HashMap, ops};

use ast_utils::{flatten_paren, get_str_literal, name_of_ident};
use id_arena::{Arena, Id};
use rnix::NixLanguage;

pub type Name = String; // TODO: might need other stuff?

pub type ExprId = Id<Expr>;
pub type NameId = Id<Name>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    exprs: Arena<Expr>,
    names: Arena<Name>,
    entry_expr: ExprId,
}

impl ops::Index<ExprId> for Module {
    type Output = Expr;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

impl ops::Index<NameId> for Module {
    type Output = Name;
    fn index(&self, index: NameId) -> &Self::Output {
        &self.names[index]
    }
}

pub type AstPtr = rowan::ast::SyntaxNodePtr<NixLanguage>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ModuleSourceMap {
    expr_map: HashMap<AstPtr, ExprId>,
    expr_map_rev: HashMap<ExprId, AstPtr>,
    name_map: HashMap<AstPtr, NameId>,
    name_map_rev: HashMap<NameId, AstPtr>, // TODO: nil has this a Vec<AstPtr>, will probs matter later
}

impl ModuleSourceMap {
    pub fn shrink_to_fit(&mut self) {
        self.expr_map.shrink_to_fit();
        self.expr_map_rev.shrink_to_fit();
        self.name_map.shrink_to_fit();
        self.name_map_rev.shrink_to_fit();
    }

    pub fn expr_for_node(&self, node: AstPtr) -> Option<ExprId> {
        self.expr_map.get(&node).copied()
    }

    pub fn node_for_expr(&self, expr_id: ExprId) -> Option<AstPtr> {
        self.expr_map_rev.get(&expr_id).cloned()
    }

    pub fn name_for_node(&self, node: AstPtr) -> Option<NameId> {
        self.name_map.get(&node).copied()
    }

    pub fn nodes_for_name(&self, name_id: NameId) -> impl Iterator<Item = AstPtr> + '_ {
        self.name_map_rev
            .get(&name_id)
            .into_iter()
            // .flatten()
            .cloned()
    }

    pub fn insert_expr(&mut self, expr: ExprId, ptr: AstPtr) {
        self.expr_map.insert(ptr, expr);
        self.expr_map_rev.insert(expr, ptr);
    }

    pub fn insert_name(&mut self, name: NameId, ptr: AstPtr) {
        self.name_map.insert(ptr, name);
        self.name_map_rev.insert(name, ptr);
    }
}

type NixPath = String; // TODO: realt type

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Literal {
    Float(ordered_float::OrderedFloat<f64>),
    Integer(i64),
    String(String),
    Path(NixPath),
    Uri, // TODO:
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pat {
    pub fields: Box<[(Option<NameId>, Option<ExprId>)]>,
    pub ellipsis: bool,
}
pub type Attrpath = Box<[ExprId]>;

type Param = String; // TODO: real type

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Missing, // for an invalid parsed expression. Allows us to parse as much as we can and leave "holes"
    Apply {
        fun: ExprId,
        arg: ExprId,
    },
    Literal(Literal),
    Lambda {
        param: Param,
        body: ExprId,
    },
    LetIn {
        bindings: Bindings,
        body: ExprId,
    },
    List(Box<[ExprId]>),
    BinOp {
        lhs: ExprId,
        rhs: ExprId,
        op: rnix::ast::BinOpKind,
    },
    AttrSet {
        is_rec: bool,
        bindings: Bindings,
    },
    UnaryOp {
        op: rnix::ast::UnaryOpKind,
        expr: ExprId,
    },
    Reference(String),

    Select {
        set: ExprId,
        attrpath: Attrpath,
        default_expr: Option<ExprId>,
    },

    StringInterpolation(Box<[InterpolPart<String>]>),
    PathInterpolation(Box<[InterpolPart<String>]>),
    // not mapped yet
    // Select
    // Error
    // Assert
    // With
    // HasAttr

    // not sure if needed
    // Root
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpolPart<T> {
    Literal(T),
    Interpol(ExprId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bindings {
    pub statics: Box<[(NameId, BindingValue)]>,
    pub inherit_froms: Box<[ExprId]>,
    pub dynamics: Box<[(ExprId, ExprId)]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BindingValue {
    Expr(ExprId),
    Inherit(ExprId),
    // TODO: could we just have a ref to the expr id directly here
    // this approach makes sure we only "deal" with the expr inside the inherit once
    // and makes walking the tree a little nicer
    InheritFrom(usize), // index in the inherit_froms list
}

impl Bindings {
    pub fn walk_child_exprs(&self, mut f: impl FnMut(ExprId)) {
        for (_, value) in self.statics.iter() {
            match value {
                BindingValue::Inherit(e) | BindingValue::Expr(e) => f(*e),
                BindingValue::InheritFrom(_idx) => {}
            }
        }
        for &e in self.inherit_froms.iter() {
            f(e);
        }
        for &(k, v) in self.dynamics.iter() {
            f(k);
            f(v);
        }
    }

    // FIXME: This is currently O(n).
    pub fn get(&self, name: &str, module: &Module) -> Option<BindingValue> {
        self.statics
            .iter()
            .find_map(|&(name_id, value)| (module[name_id] == name).then_some(value))
    }
}
