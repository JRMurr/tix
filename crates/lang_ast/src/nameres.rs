use std::{collections::HashMap, iter, ops};

use la_arena::{Arena, Idx as Id};
use petgraph::graph::DiGraph;
use smol_str::SmolStr;

use super::{BindingValue, Expr, ExprId, Module, NameId};
use crate::{db::NixFile, module, Bindings};

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

// ==============================================================================
// Builtin Metadata
// ==============================================================================

/// Returns the static name string if `name` is a known global builtin
/// (i.e. available without the `builtins.` prefix in Nix).
pub fn lookup_global_builtin(name: &str) -> Option<&'static str> {
    match name {
        "abort" => Some("abort"),
        "baseNameOf" => Some("baseNameOf"),
        "derivation" => Some("derivation"),
        "dirOf" => Some("dirOf"),
        "fetchGit" => Some("fetchGit"),
        "fetchMercurial" => Some("fetchMercurial"),
        "fetchTarball" => Some("fetchTarball"),
        "fetchTree" => Some("fetchTree"),
        "fetchurl" => Some("fetchurl"),
        "fromTOML" => Some("fromTOML"),
        "import" => Some("import"),
        "isNull" => Some("isNull"),
        "map" => Some("map"),
        "placeholder" => Some("placeholder"),
        "removeAttrs" => Some("removeAttrs"),
        "scopedImport" => Some("scopedImport"),
        "throw" => Some("throw"),
        "toString" => Some("toString"),
        _ => None,
    }
}

#[salsa::tracked]
pub fn scopes(db: &dyn crate::AstDb, file: NixFile) -> ModuleScopes {
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
        if let Some(static_name) = lookup_global_builtin(name) {
            return Some(ResolveResult::Builtin(static_name));
        }
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

        // TODO: If this is a non-rec attr i don't think this scope should be used below?
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
pub fn name_resolution(db: &dyn crate::AstDb, file: NixFile) -> NameResolution {
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

    #[allow(dead_code)]
    pub fn iter(&self) -> impl Iterator<Item = (ExprId, &'_ ResolveResult)> + '_ {
        self.resolve_map
            .iter()
            .filter_map(|(e, res)| Some((*e, res.as_ref()?)))
    }
}

// TODO: need a way to also track dynamic attrset keys when the attrset is defined as rec
// could abstract to a "Identifiable" type thats NameId | ExprID
// figuring out deps could get weird but doesn't seem wild

#[derive(Debug)]
struct NameDependencies {
    edges: Vec<(NameId, NameId)>, // (from, to)
    // dep_graph: DepGraph,
    name_to_expr: HashMap<NameId, ExprId>,
    // name_to_node_id: HashMap<NameId, NodeIndex<DefaultIx>>,
}

impl NameDependencies {
    pub fn new(module: &Module, name_res: &NameResolution) -> Self {
        // let num_names = module.names.len(); // number of nodes
        let num_refs = name_res.resolve_map.len(); // upper bound on the number of edges

        // let mut dep_graph = DepGraph::with_capacity(num_names, num_refs);
        // let mut name_to_node_id = HashMap::new();

        // for (name_id, _) in module.names() {
        //     let node_id = dep_graph.add_node(());
        //     name_to_node_id.insert(name_id, node_id);
        // }

        let mut name_deps = Self {
            edges: Vec::with_capacity(num_refs),
            // dep_graph,
            name_to_expr: HashMap::new(),
            // name_to_node_id,
        };

        name_deps.traverse_expr(module, name_res, module.entry_expr, None);

        name_deps
    }

    fn traverse_expr(
        &mut self,
        module: &Module,
        name_res: &NameResolution,
        expr: ExprId,
        curr_binding: Option<NameId>,
    ) {
        match &module[expr] {
            // If we are not in a let block (ie not curr_binding)
            // we can ignore references (just referencing the args of a root function)
            Expr::Reference(_name_str) if curr_binding.is_some() => {
                let curr_binding = curr_binding.unwrap();
                let resolve_res = if let Some(name_ref) = name_res.get(expr) {
                    name_ref
                } else {
                    return;
                };

                match resolve_res {
                    ResolveResult::Definition(id) => {
                        // TODO: we don't want to push an edge if the resolved ref
                        // is a function param. For now we filter it out when walking the
                        // scc but would be nice to do from the beginning
                        self.edges.push((curr_binding, *id));
                    }
                    ResolveResult::Builtin(_) => {
                        // Builtins don't depend on user-defined names; nothing to record.
                    }
                    ResolveResult::WithExprs(_vec) => todo!(),
                }
            }
            Expr::LetIn { bindings, body } => {
                self.traverse_bindings(module, name_res, bindings);
                self.traverse_expr(module, name_res, *body, curr_binding);
            }
            Expr::AttrSet { bindings, is_rec } => {
                // if its not recursive we wont do generalization on each key
                // TODO: this might be weird but seems like a good approach for now
                if *is_rec {
                    self.traverse_bindings(module, name_res, bindings)
                } else {
                    bindings.walk_child_exprs(|e| {
                        self.traverse_expr(module, name_res, e, curr_binding)
                    });
                }
            }
            expr => {
                expr.walk_child_exprs(|e| self.traverse_expr(module, name_res, e, curr_binding))
            }
        }
    }

    fn traverse_bindings(
        &mut self,
        module: &Module,
        name_res: &NameResolution,
        bindings: &Bindings,
        // expr: ExprId,
    ) {
        for (name, bv) in &bindings.statics {
            let expr = match bv {
                BindingValue::Expr(id) => *id,
                BindingValue::Inherit(id) => *id,
                BindingValue::InheritFrom(id) => *id,
            };

            self.name_to_expr.insert(*name, expr);
            self.traverse_expr(module, name_res, expr, Some(*name));
        }
        for (_name_expr, _value_expr) in bindings.dynamics.iter() {
            todo!()
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeDef {
    name: NameId,
    value: ExprId,
}

impl TypeDef {
    pub fn expr(&self) -> ExprId {
        self.value
    }

    pub fn name(&self) -> NameId {
        self.name
    }
}

/// Names that should be inferred and generalized as a group since the defs inside are mutually dependent
pub type DependentGroup = Vec<TypeDef>;

pub type GroupedDefs = Vec<DependentGroup>;
type DepGraph = DiGraph<NameId, ()>;

#[salsa::tracked]
pub fn group_def(db: &dyn crate::AstDb, file: NixFile) -> GroupedDefs {
    let module = module(db, file);
    let name_res = name_resolution(db, file);

    let name_deps = NameDependencies::new(&module, &name_res);

    let num_names = name_deps.name_to_expr.len();
    let num_refs = name_deps.edges.len();

    let mut dep_graph = DepGraph::with_capacity(num_names, num_refs);
    // TODO: there is def a better way to do this but don't care right now
    let mut name_to_node_id = HashMap::new();
    // let mut node_id_to_name = HashMap::new();

    // let tmp: Vec<_> = module.names().collect();
    // dbg!(tmp);

    for (name_id, _) in module.names() {
        let node_id = dep_graph.add_node(name_id);
        name_to_node_id.insert(name_id, node_id);

        // make sure every name shows up
        dep_graph.add_edge(node_id, node_id, ());
    }

    // for name_id in name_deps.name_to_expr.keys() {
    //     // dbg!((name_id, name));
    //     let node_id = dep_graph.add_node(*name_id);
    //     name_to_node_id.insert(name_id, node_id);
    //     // node_id_to_name.insert(node_id, name_id);
    // }

    for (from, to) in name_deps.edges {
        let from = name_to_node_id.get(&from).unwrap();
        let to = name_to_node_id.get(&to).unwrap();

        dep_graph.add_edge(*from, *to, ());
    }

    let scc = petgraph::algo::tarjan_scc(&dep_graph);

    let scc: GroupedDefs = scc
        .iter()
        .flat_map(|group| {
            let mapped_group: Vec<_> = group
                .iter()
                .flat_map(|n| {
                    let name = dep_graph[*n];
                    let expr = name_deps.name_to_expr.get(&name);
                    // TODO: do this check earlier, at the very least could be done when we add edges
                    // If the expr is not found for the name then it was a func param we can ignore
                    expr.map(|e| TypeDef { name, value: *e })
                })
                .collect();
            if mapped_group.is_empty() {
                None
            } else {
                Some(mapped_group)
            }
        })
        .collect();

    scc
}
