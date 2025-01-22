// A lot of the code in this module is based on
// https://github.com/oxalica/nil/tree/main/crates/ide/src/def

// pub mod expr_table;
mod ast_utils;
mod comment;
mod db;
mod lower;
mod nameres;
mod ty;

#[cfg(test)]
mod tests;

use std::{collections::HashMap, ops};

use comment::gather_doc_comments;
use db::NixFile;
pub use db::{Db, RootDatabase};
// use derive_more::Debug;
use la_arena::{Arena, ArenaMap, Idx as Id};
use lower::lower;
pub use nameres::scopes;
use rnix::NixLanguage;
use smol_str::SmolStr;
pub use ty::*;

#[salsa::tracked]
pub fn module_and_source_maps(db: &dyn crate::Db, file: NixFile) -> (Module, ModuleSourceMap) {
    let root = db.parse_file(file);

    let docs = gather_doc_comments(&root);

    lower(root, docs)
}

#[salsa::tracked]
pub fn module(db: &dyn crate::Db, file: NixFile) -> Module {
    module_and_source_maps(db, file).0
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name {
    pub text: SmolStr,
    pub kind: NameKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NameKind {
    LetIn,
    PlainAttrset,
    RecAttrset,
    Param,
    PatField,
}

impl NameKind {
    pub fn is_definition(self) -> bool {
        !matches!(self, Self::PlainAttrset)
    }
}

// TODO: @OPTIMIZATION look into using a custom Id type. Since the default Id from id-arena has the arena id in
// salsa will basically always have a cache miss since every parse will cause a new arena to spawn
pub type ExprId = Id<Expr>;
pub type NameId = Id<Name>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    exprs: Arena<Expr>,
    names: Arena<Name>,
    pub entry_expr: ExprId,
    type_dec_map: ModuleTypeDecMap,
}

impl Module {
    pub fn exprs(&self) -> impl ExactSizeIterator<Item = (ExprId, &Expr)> {
        self.exprs.iter()
    }

    pub fn names(&self) -> impl ExactSizeIterator<Item = (NameId, &Name)> {
        self.names.iter()
    }
}

// impl Module {
//     pub fn walk_module(&self, mut f: impl FnMut(&Expr)) {
//         let expr = &self.exprs[self.entry_expr];
//         expr.walk_child_exprs(|child| {
//             let child_expr = &self.exprs[child];
//             child_expr.walk_child_exprs(f);
//         });
//     }
// }

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

pub type DocComment = String; // TODO: real type

pub type DocComments = Vec<DocComment>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ModuleTypeDecMap {
    expr_map: ArenaMap<ExprId, DocComments>,
    name_map: ArenaMap<NameId, DocComments>,
}

impl ModuleTypeDecMap {
    pub fn docs_for_expr(&self, expr_id: ExprId) -> Option<&DocComments> {
        self.expr_map.get(expr_id)
    }

    pub fn insert_expr(&mut self, expr_id: ExprId, comments: DocComments) {
        self.expr_map.insert(expr_id, comments);
    }

    pub fn docs_for_name(&self, name_id: NameId) -> Option<&DocComments> {
        self.name_map.get(name_id)
    }

    pub fn insert_name(&mut self, name_id: NameId, comments: DocComments) {
        self.name_map.insert(name_id, comments);
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ModuleSourceMap {
    expr_map: HashMap<AstPtr, ExprId>,
    expr_map_rev: ArenaMap<ExprId, AstPtr>,
    name_map: HashMap<AstPtr, NameId>,
    name_map_rev: ArenaMap<NameId, AstPtr>, // TODO: nil has this a Vec<AstPtr>, will probs matter later
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
        self.expr_map_rev.get(expr_id).cloned()
    }

    pub fn name_for_node(&self, node: AstPtr) -> Option<NameId> {
        self.name_map.get(&node).copied()
    }

    pub fn nodes_for_name(&self, name_id: NameId) -> impl Iterator<Item = AstPtr> + '_ {
        self.name_map_rev
            .get(name_id)
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

// fn module_with_source_map(
//     db: &dyn crate::Db,
//     file_id: FileId,
// ) -> (Arc<Module>, Arc<ModuleSourceMap>) {
//     let parse = db.parse(file_id);
//     let (mut module, mut source_map) = lower::lower(db, file_id, parse);
//     module.shrink_to_fit();
//     source_map.shrink_to_fit();
//     (Arc::new(module), Arc::new(source_map))
// }

type NixPath = String; // TODO: real type

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Literal {
    Float(ordered_float::OrderedFloat<f64>),
    Integer(i64),
    String(SmolStr),
    Path(NixPath),
    Uri, // TODO:
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pat {
    pub fields: Box<[(Option<NameId>, Option<ExprId>)]>,
    pub ellipsis: bool,
}
pub type Attrpath = Box<[ExprId]>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Missing, // for an invalid parsed expression. Allows us to parse as much as we can and leave "holes"
    Apply {
        fun: ExprId,
        arg: ExprId,
    },
    IfThenElse {
        cond: ExprId,
        then_body: ExprId,
        else_body: ExprId,
    },
    Literal(Literal),
    Lambda {
        // at least one of these should be set, if both are they should be the same "type"
        param: Option<NameId>,
        pat: Option<Pat>,
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
        op: BinOP,
    },
    AttrSet {
        is_rec: bool,
        bindings: Bindings,
    },
    UnaryOp {
        op: rnix::ast::UnaryOpKind,
        expr: ExprId,
    },
    Reference(SmolStr),
    Select {
        set: ExprId,
        attrpath: Attrpath,
        default_expr: Option<ExprId>,
    },
    HasAttr {
        set: ExprId,
        attrpath: Attrpath,
    },
    With {
        env: ExprId,
        body: ExprId,
    },
    Assert {
        cond: ExprId,
        body: ExprId,
    },
    StringInterpolation(Box<[InterpolPart<SmolStr>]>),
    PathInterpolation(Box<[InterpolPart<SmolStr>]>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OverloadBinOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl OverloadBinOp {
    pub fn is_add(&self) -> bool {
        matches!(self, OverloadBinOp::Add)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolBinOp {
    And,
    Implication,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprBinOp {
    Less,
    LessOrEq,
    More,
    MoreOrEq,
    NotEqual,
    Equal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalBinOp {
    Expr(ExprBinOp),
    Bool(BoolBinOp),
    ListConcat,
    AttrUpdate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOP {
    Overload(OverloadBinOp),
    Normal(NormalBinOp),
}

impl From<rnix::ast::BinOpKind> for BinOP {
    fn from(value: rnix::ast::BinOpKind) -> Self {
        match value {
            rnix::ast::BinOpKind::Concat => BinOP::Normal(NormalBinOp::ListConcat),
            rnix::ast::BinOpKind::Update => BinOP::Normal(NormalBinOp::AttrUpdate),

            rnix::ast::BinOpKind::Add => BinOP::Overload(OverloadBinOp::Add),
            rnix::ast::BinOpKind::Sub => BinOP::Overload(OverloadBinOp::Sub),
            rnix::ast::BinOpKind::Mul => BinOP::Overload(OverloadBinOp::Mul),
            rnix::ast::BinOpKind::Div => BinOP::Overload(OverloadBinOp::Div),

            rnix::ast::BinOpKind::And => BinOP::Normal(NormalBinOp::Bool(BoolBinOp::And)),
            rnix::ast::BinOpKind::Or => BinOP::Normal(NormalBinOp::Bool(BoolBinOp::Or)),
            rnix::ast::BinOpKind::Implication => {
                BinOP::Normal(NormalBinOp::Bool(BoolBinOp::Implication))
            }

            rnix::ast::BinOpKind::Equal => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::Equal)),
            rnix::ast::BinOpKind::Less => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::Less)),
            rnix::ast::BinOpKind::LessOrEq => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::LessOrEq)),
            rnix::ast::BinOpKind::More => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::More)),
            rnix::ast::BinOpKind::MoreOrEq => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::MoreOrEq)),
            rnix::ast::BinOpKind::NotEqual => BinOP::Normal(NormalBinOp::Expr(ExprBinOp::NotEqual)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bindings {
    pub statics: Box<[(NameId, BindingValue)]>,
    pub inherit_froms: Box<[ExprId]>,
    pub dynamics: Box<[(ExprId, ExprId)]>,
}

impl Bindings {
    /// Returns (name, value_expr) for all non dynamic bindings
    pub fn name_values(&self) -> impl Iterator<Item = (NameId, ExprId)> {
        self.statics.iter().map(|(name, bv)| match &bv {
            BindingValue::Expr(id) => (*name, *id),
            BindingValue::Inherit(id) => (*name, *id),
            BindingValue::InheritFrom(idx) => (*name, self.inherit_froms[*idx]),
        })
    }
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
            .find_map(|&(name_id, value)| (module[name_id].text == name).then_some(value))
    }
}

impl Expr {
    pub fn walk_child_exprs(&self, mut f: impl FnMut(ExprId)) {
        match self {
            Self::Missing | Self::Reference(_) | Self::Literal(_) => {}
            Self::Lambda {
                pat,
                body,
                param: _,
            } => {
                if let Some(p) = pat {
                    p.fields
                        .iter()
                        .filter_map(|&(_, default_expr)| default_expr)
                        .for_each(&mut f);
                }
                f(*body);
            }
            Self::UnaryOp { expr, op: _ } => f(*expr),
            Self::Assert { body: a, cond: b }
            | Self::With { env: a, body: b }
            | Self::BinOp {
                lhs: a,
                rhs: b,
                op: _,
            }
            | Self::Apply { fun: a, arg: b } => {
                f(*a);
                f(*b);
            }
            Self::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                f(*cond);
                f(*then_body);
                f(*else_body);
            }
            Self::HasAttr { set, attrpath } => {
                f(*set);
                attrpath.iter().copied().for_each(f);
            }
            Self::Select {
                set,
                attrpath,
                default_expr,
            } => {
                f(*set);
                attrpath.iter().copied().for_each(&mut f);
                if let &Some(e) = default_expr {
                    f(e);
                }
            }
            Self::List(xs) => {
                xs.iter().copied().for_each(f);
            }
            Self::LetIn { bindings, body } => {
                bindings.walk_child_exprs(&mut f);
                f(*body);
            }
            Self::AttrSet {
                is_rec: _,
                bindings,
            } => {
                bindings.walk_child_exprs(f);
            }
            Self::StringInterpolation(parts) | Self::PathInterpolation(parts) => {
                for part in parts.iter() {
                    if let InterpolPart::Interpol(e) = part {
                        f(*e)
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpolPart<T> {
    Literal(T),
    Interpol(ExprId),
}
