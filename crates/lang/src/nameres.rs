use std::{collections::HashMap, iter, ops};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use crate::{Bindings, db::NixFile, module};

use super::{BindingValue, Expr, ExprId, Module, NameId};

pub type ScopeId = Id<ScopeData>;

impl ops::Index<ScopeId> for ModuleScopes {
    type Output = ScopeData;
    fn index(&self, index: ScopeId) -> &Self::Output {
        &self.scopes[index]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeData {
    parent: Option<ScopeId>,
    kind: ScopeKind,
}

impl ScopeData {
    pub fn as_definitions(&self) -> Option<&HashMap<SmolStr, NameId>> {
        match &self.kind {
            ScopeKind::Definitions(defs) => Some(defs),
            _ => None,
        }
    }

    pub fn as_with(&self) -> Option<ExprId> {
        match self.kind {
            ScopeKind::WithExpr(expr) => Some(expr),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ScopeKind {
    Definitions(HashMap<SmolStr, NameId>),
    WithExpr(ExprId),
}

/// The resolve result of a name reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveResult {
    /// Reference to a Name.
    Definition(NameId),
    /// Reference to a builtin value.
    Builtin(&'static str),
    /// Attr of one of some `with` expressions, from innermost to outermost.
    /// It must not be empty.
    WithExprs(Vec<ExprId>),
}

#[salsa::tracked]
pub fn scopes(db: &dyn crate::Db, file: NixFile) -> ModuleScopes {
    let module = crate::module(db, file);
    ModuleScopes::new(module)
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ModuleScopes {
    pub scopes: Arena<ScopeData>,
    pub scope_by_expr: HashMap<ExprId, ScopeId>,
}

impl ModuleScopes {
    pub fn new(module: Module) -> Self {
        let mut ms = ModuleScopes {
            scopes: Arena::new(),
            scope_by_expr: HashMap::with_capacity(module.exprs.len()),
        };
        let root_scope = ms.scopes.alloc(ScopeData {
            parent: None,
            kind: ScopeKind::Definitions(Default::default()),
        });
        ms.traverse_expr(&module, module.entry_expr, root_scope);

        ms
    }

    pub fn scope_for_expr(&self, expr_id: ExprId) -> Option<ScopeId> {
        self.scope_by_expr.get(&expr_id).copied()
    }

    pub fn ancestors(&self, scope_id: ScopeId) -> impl Iterator<Item = &'_ ScopeData> + '_ {
        iter::successors(Some(scope_id), |&i| self[i].parent).map(|i| &self[i])
    }

    /// Resolve a name in the scope of an Expr.
    fn resolve_name(&self, expr_id: ExprId, name: &SmolStr) -> Option<ResolveResult> {
        let scope = self.scope_for_expr(expr_id)?;
        // 1. Local defs.
        if let Some(name) = self
            .ancestors(scope)
            .find_map(|data| data.as_definitions()?.get(name))
        {
            return Some(ResolveResult::Definition(*name));
        }
        // 2. Global builtin names.
        // if let Some((name, b)) = ALL_BUILTINS.get_entry(name) {
        //     if b.is_global {
        //         return Some(ResolveResult::Builtin(name));
        //     }
        // }
        // 3. "with" exprs.
        let withs = self
            .ancestors(scope)
            .filter_map(|data| data.as_with())
            .collect::<Vec<_>>();
        if !withs.is_empty() {
            return Some(ResolveResult::WithExprs(withs));
        }
        None
    }

    fn traverse_expr(&mut self, module: &Module, expr: ExprId, scope: ScopeId) {
        self.scope_by_expr.insert(expr, scope);

        match &module[expr] {
            Expr::Lambda { param, pat, body } => {
                let mut defs = HashMap::default();
                if let &Some(name_id) = param {
                    defs.insert(module[name_id].text.clone(), name_id);
                }
                if let Some(pat) = pat {
                    for name_id in pat.fields.iter().filter_map(|(opt_id, _)| *opt_id) {
                        defs.insert(module[name_id].text.clone(), name_id);
                    }
                }

                let scope = if !defs.is_empty() {
                    self.scopes.alloc(ScopeData {
                        parent: Some(scope),
                        kind: ScopeKind::Definitions(defs),
                    })
                } else {
                    scope
                };

                if let Some(pat) = pat {
                    for default_expr in pat.fields.iter().filter_map(|(_, e)| *e) {
                        self.traverse_expr(module, default_expr, scope);
                    }
                }
                self.traverse_expr(module, *body, scope);
            }
            Expr::With { env, body } => {
                self.traverse_expr(module, *env, scope);
                let scope = self.scopes.alloc(ScopeData {
                    parent: Some(scope),
                    kind: ScopeKind::WithExpr(expr),
                });
                self.traverse_expr(module, *body, scope);
            }
            Expr::AttrSet {
                bindings,
                is_rec: _,
            } => {
                self.traverse_bindings(module, bindings, scope);
            }
            Expr::LetIn { bindings, body } => {
                let scope = self.traverse_bindings(module, bindings, scope);
                self.traverse_expr(module, *body, scope);
            }
            e => e.walk_child_exprs(|e| self.traverse_expr(module, e, scope)),
        }
    }

    fn traverse_bindings(
        &mut self,
        module: &Module,
        bindings: &Bindings,
        scope: ScopeId,
    ) -> ScopeId {
        let mut defs = HashMap::default();

        for &(name, value) in bindings.statics.iter() {
            if module[name].kind.is_definition() {
                defs.insert(module[name].text.clone(), name);
            }

            // Inherited attrs are resolved in the outer scope.
            if let BindingValue::Inherit(expr) = value {
                assert!(matches!(&module[expr], Expr::Reference(_)));
                self.traverse_expr(module, expr, scope);
            }
        }

        let scope = if defs.is_empty() {
            scope
        } else {
            self.scopes.alloc(ScopeData {
                parent: Some(scope),
                kind: ScopeKind::Definitions(defs),
            })
        };

        for &(_, value) in bindings.statics.iter() {
            match value {
                    // Traversed before.
                    BindingValue::Inherit(_) |
                    // Traversed later.
                    BindingValue::InheritFrom(_) => {},
                    BindingValue::Expr(e) => {
                        self.traverse_expr(module, e, scope);
                    }
                }
        }
        for &e in bindings.inherit_froms.iter() {
            self.traverse_expr(module, e, scope);
        }
        for &(k, v) in bindings.dynamics.iter() {
            self.traverse_expr(module, k, scope);
            self.traverse_expr(module, v, scope);
        }
        scope
    }
}

/// Name resolution of all references.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct NameResolution {
    // `None` value for unresolved names.
    resolve_map: HashMap<ExprId, Option<ResolveResult>>,
    // // All names from the common pattern `inherit (builtins) ...`.
    // // This is used for tracking builtins names even through aliasing.
    // inherited_builtins: HashSet<NameId>,
}

#[salsa::tracked]
pub fn name_resolution(db: &dyn crate::Db, file: NixFile) -> NameResolution {
    let module = module(db, file);
    let scopes = scopes(db, file);
    let resolve_map = module
        .exprs()
        .filter_map(|(e, kind)| {
            match kind {
                // Inherited attrs are also translated into Expr::References.
                Expr::Reference(name) => Some((e, scopes.resolve_name(e, name))),
                _ => None,
            }
        })
        .collect::<HashMap<_, _>>();

    NameResolution { resolve_map }
}

impl NameResolution {
    pub fn get(&self, expr: ExprId) -> Option<&ResolveResult> {
        self.resolve_map.get(&expr)?.as_ref()
    }

    pub fn iter(&self) -> impl Iterator<Item = (ExprId, &'_ ResolveResult)> + '_ {
        self.resolve_map
            .iter()
            .filter_map(|(e, res)| Some((*e, res.as_ref()?)))
    }
}
