use std::{collections::HashMap, iter, ops};

use la_arena::{Arena, ArenaMap, Idx as Id};
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
    /// Attr of one or more `with` expressions, from innermost to outermost.
    /// The first element is the innermost; the rest are outer fallbacks.
    WithExprs(ExprId, Vec<ExprId>),
}

// ==============================================================================
// Builtin Metadata
// ==============================================================================

/// All global builtin names (available without the `builtins.` prefix in Nix).
/// Derived from the match arms in `lookup_global_builtin`.
pub const GLOBAL_BUILTIN_NAMES: &[&str] = &[
    "abort",
    "baseNameOf",
    "derivation",
    "dirOf",
    "false",
    "fetchGit",
    "fetchMercurial",
    "fetchTarball",
    "fetchTree",
    "fetchurl",
    "fromTOML",
    "import",
    "isNull",
    "map",
    "null",
    "placeholder",
    "removeAttrs",
    "scopedImport",
    "throw",
    "toString",
    "true",
];

/// Returns the static name string if `name` is a known global builtin
/// (i.e. available without the `builtins.` prefix in Nix).
pub fn lookup_global_builtin(name: &str) -> Option<&'static str> {
    match name {
        "abort" => Some("abort"),
        "baseNameOf" => Some("baseNameOf"),
        "derivation" => Some("derivation"),
        "dirOf" => Some("dirOf"),
        "false" => Some("false"),
        "fetchGit" => Some("fetchGit"),
        "fetchMercurial" => Some("fetchMercurial"),
        "fetchTarball" => Some("fetchTarball"),
        "fetchTree" => Some("fetchTree"),
        "fetchurl" => Some("fetchurl"),
        "fromTOML" => Some("fromTOML"),
        "import" => Some("import"),
        "isNull" => Some("isNull"),
        "map" => Some("map"),
        "null" => Some("null"),
        "placeholder" => Some("placeholder"),
        "removeAttrs" => Some("removeAttrs"),
        "scopedImport" => Some("scopedImport"),
        "throw" => Some("throw"),
        "toString" => Some("toString"),
        "true" => Some("true"),
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
    pub scope_by_expr: ArenaMap<ExprId, ScopeId>,
}

impl ModuleScopes {
    pub fn new(module: Module) -> Self {
        let mut ms = ModuleScopes {
            scopes: Arena::new(),
            scope_by_expr: ArenaMap::with_capacity(module.exprs.len()),
        };
        let root_scope = ms.scopes.alloc(ScopeData {
            parent: None,
            kind: ScopeKind::Definitions(Default::default()),
        });
        ms.traverse_expr(&module, module.entry_expr, root_scope);

        ms
    }

    pub fn scope_for_expr(&self, expr_id: ExprId) -> Option<ScopeId> {
        self.scope_by_expr.get(expr_id).copied()
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
        let mut withs = self.ancestors(scope).filter_map(|data| data.as_with());
        if let Some(innermost) = withs.next() {
            return Some(ResolveResult::WithExprs(innermost, withs.collect()));
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

        // This is correct for non-rec attrsets: PlainAttrset.is_definition()
        // returns false, so `defs` is empty and we reuse the parent scope.
        // Only rec-attrsets and let-in bindings populate `defs`.
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
    /// `None` value for unresolved names.
    resolve_map: ArenaMap<ExprId, Option<ResolveResult>>,
    /// Inverted index: for each NameId, the ExprIds that resolve to it.
    /// Built once during name_resolution() so callers avoid repeated O(n) scans.
    refs_by_name: HashMap<NameId, Vec<ExprId>>,
}

#[salsa::tracked]
pub fn name_resolution(db: &dyn crate::AstDb, file: NixFile) -> NameResolution {
    let module = module(db, file);
    let scopes = scopes(db, file);
    let resolve_map: ArenaMap<_, _> = module
        .exprs()
        .filter_map(|(e, kind)| {
            match kind {
                // Inherited attrs are also translated into Expr::References.
                Expr::Reference(name) => Some((e, scopes.resolve_name(e, name))),
                _ => None,
            }
        })
        .collect();

    // Build the inverted index: NameId → Vec<ExprId>.
    let mut refs_by_name: HashMap<NameId, Vec<ExprId>> = HashMap::new();
    for (expr_id, resolved) in resolve_map.iter() {
        if let Some(ResolveResult::Definition(name_id)) = resolved {
            refs_by_name.entry(*name_id).or_default().push(expr_id);
        }
    }

    NameResolution {
        resolve_map,
        refs_by_name,
    }
}

impl NameResolution {
    pub fn get(&self, expr: ExprId) -> Option<&ResolveResult> {
        self.resolve_map.get(expr)?.as_ref()
    }

    #[allow(dead_code)]
    pub fn iter(&self) -> impl Iterator<Item = (ExprId, &'_ ResolveResult)> + '_ {
        self.resolve_map
            .iter()
            .filter_map(|(e, res)| Some((e, res.as_ref()?)))
    }

    /// All reference ExprIds that resolve to the given NameId.
    pub fn refs_to(&self, name: NameId) -> &[ExprId] {
        self.refs_by_name.get(&name).map_or(&[], |v| v.as_slice())
    }
}

// TODO: need a way to also track dynamic attrset keys when the attrset is defined as rec
// could abstract to a "Identifiable" type thats NameId | ExprID
// figuring out deps could get weird but doesn't seem wild

#[derive(Debug)]
struct NameDependencies {
    edges: Vec<(NameId, NameId)>,
    name_to_expr: HashMap<NameId, ExprId>,
    /// Narrowing scopes for each binding: records which NarrowBindings are
    /// active when a let/rec-attrset binding is encountered. Populated by
    /// traverse_expr as it walks through if-then-else, assert, and
    /// conditional-apply scopes.
    narrow_scopes: HashMap<NameId, Vec<crate::narrow::NarrowBinding>>,
}

impl NameDependencies {
    pub fn new(
        module: &Module,
        name_res: &NameResolution,
        binding_exprs: &HashMap<NameId, ExprId>,
    ) -> Self {
        let mut name_deps = Self {
            edges: Vec::with_capacity(module.exprs.len()),
            name_to_expr: HashMap::new(),
            narrow_scopes: HashMap::new(),
        };

        name_deps.traverse_expr(
            module,
            name_res,
            binding_exprs,
            module.entry_expr,
            None,
            &[],
        );

        name_deps
    }

    fn traverse_expr(
        &mut self,
        module: &Module,
        name_res: &NameResolution,
        binding_exprs: &HashMap<NameId, ExprId>,
        expr: ExprId,
        curr_binding: Option<NameId>,
        active: &[crate::narrow::NarrowBinding],
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
                    ResolveResult::WithExprs(..) => {
                        // No dependency edge needed: the env expression's own
                        // dependencies are already captured via walk_child_exprs
                        // in the Expr::With fallthrough arm.
                    }
                }
            }

            // ── IfThenElse — analyze condition, push narrowings per branch
            Expr::IfThenElse {
                cond,
                then_body,
                else_body,
            } => {
                self.traverse_expr(module, name_res, binding_exprs, *cond, curr_binding, active);
                let info = crate::narrow::analyze_condition(module, name_res, binding_exprs, *cond);

                let mut then_active = active.to_vec();
                then_active.extend(info.then_branch);
                self.traverse_expr(
                    module,
                    name_res,
                    binding_exprs,
                    *then_body,
                    curr_binding,
                    &then_active,
                );

                let mut else_active = active.to_vec();
                else_active.extend(info.else_branch);
                self.traverse_expr(
                    module,
                    name_res,
                    binding_exprs,
                    *else_body,
                    curr_binding,
                    &else_active,
                );
            }

            // ── Assert — condition narrowing applies to body
            Expr::Assert { cond, body } => {
                self.traverse_expr(module, name_res, binding_exprs, *cond, curr_binding, active);
                let info = crate::narrow::analyze_condition(module, name_res, binding_exprs, *cond);
                let mut body_active = active.to_vec();
                body_active.extend(info.then_branch);
                self.traverse_expr(
                    module,
                    name_res,
                    binding_exprs,
                    *body,
                    curr_binding,
                    &body_active,
                );
            }

            // ── Apply — detect conditional library functions
            Expr::Apply { fun, arg } => {
                let narrow_info = crate::narrow::detect_conditional_apply_narrowing(
                    module,
                    name_res,
                    binding_exprs,
                    *fun,
                );

                self.traverse_expr(module, name_res, binding_exprs, *fun, curr_binding, active);

                if let Some(info) = narrow_info {
                    let mut arg_active = active.to_vec();
                    arg_active.extend(info.then_branch);
                    self.traverse_expr(
                        module,
                        name_res,
                        binding_exprs,
                        *arg,
                        curr_binding,
                        &arg_active,
                    );
                } else {
                    self.traverse_expr(module, name_res, binding_exprs, *arg, curr_binding, active);
                }
            }

            Expr::LetIn { bindings, body } => {
                self.traverse_bindings(module, name_res, binding_exprs, bindings, active);
                self.traverse_expr(module, name_res, binding_exprs, *body, curr_binding, active);
            }
            Expr::AttrSet { bindings, is_rec } => {
                // if its not recursive we wont do generalization on each key
                // TODO: this might be weird but seems like a good approach for now
                if *is_rec {
                    self.traverse_bindings(module, name_res, binding_exprs, bindings, active)
                } else {
                    bindings.walk_child_exprs(|e| {
                        self.traverse_expr(module, name_res, binding_exprs, e, curr_binding, active)
                    });
                }
            }
            expr => expr.walk_child_exprs(|e| {
                self.traverse_expr(module, name_res, binding_exprs, e, curr_binding, active)
            }),
        }
    }

    fn traverse_bindings(
        &mut self,
        module: &Module,
        name_res: &NameResolution,
        binding_exprs: &HashMap<NameId, ExprId>,
        bindings: &Bindings,
        active: &[crate::narrow::NarrowBinding],
    ) {
        for (name, bv) in &bindings.statics {
            let expr = match bv {
                BindingValue::Expr(id) => *id,
                BindingValue::Inherit(id) => *id,
                BindingValue::InheritFrom(id) => *id,
            };

            self.name_to_expr.insert(*name, expr);

            // Record active narrowings for this binding (if any).
            if !active.is_empty() {
                self.narrow_scopes
                    .entry(*name)
                    .or_default()
                    .extend(active.iter().cloned());
            }

            self.traverse_expr(module, name_res, binding_exprs, expr, Some(*name), active);
        }
        for &(name_expr, value_expr) in bindings.dynamics.iter() {
            // Dynamic bindings have runtime-computed keys — no static NameId
            // to record dependency edges for. Traverse sub-expressions so
            // any references they contain are still captured.
            self.traverse_expr(module, name_res, binding_exprs, name_expr, None, active);
            self.traverse_expr(module, name_res, binding_exprs, value_expr, None, active);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeDef {
    name: NameId,
    value: ExprId,
    /// Narrowings active in this binding's scope (from enclosing
    /// if-then-else/assert/conditional-apply). Empty when the binding
    /// is not inside a narrowing scope.
    narrow_scope: Vec<crate::narrow::NarrowBinding>,
}

impl TypeDef {
    pub fn expr(&self) -> ExprId {
        self.value
    }

    pub fn name(&self) -> NameId {
        self.name
    }

    pub fn narrow_scope(&self) -> &[crate::narrow::NarrowBinding] {
        &self.narrow_scope
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
    let indices = crate::module_indices(db, file);

    let name_deps = NameDependencies::new(&module, &name_res, &indices.binding_expr);

    let num_names = name_deps.name_to_expr.len();
    let num_refs = name_deps.edges.len();

    let mut dep_graph = DepGraph::with_capacity(num_names, num_refs);
    let mut name_to_node_id = HashMap::new();

    for (name_id, _) in module.names() {
        let node_id = dep_graph.add_node(name_id);
        let prev = name_to_node_id.insert(name_id, node_id);
        debug_assert!(
            prev.is_none(),
            "duplicate NameId {name_id:?} in module.names() — lowering bug"
        );

        // Self-edge ensures every name appears in at least one SCC group,
        // even if it has no dependencies on other names.
        dep_graph.add_edge(node_id, node_id, ());
    }

    for (from, to) in name_deps.edges {
        // Edges may reference names outside this module (e.g. function
        // parameters that aren't tracked as module-level names). Skip
        // edges where either endpoint isn't in the dependency graph.
        let (Some(from), Some(to)) = (name_to_node_id.get(&from), name_to_node_id.get(&to)) else {
            continue;
        };

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
                    expr.map(|e| TypeDef {
                        name,
                        value: *e,
                        narrow_scope: name_deps
                            .narrow_scopes
                            .get(&name)
                            .cloned()
                            .unwrap_or_default(),
                    })
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: parse Nix source and return (db, file, module).
    fn setup(src: &str) -> (crate::RootDatabase, NixFile, crate::Module) {
        let mut db = crate::RootDatabase::default();
        let file = db.set_file_contents(std::path::PathBuf::from("/test.nix"), src.to_string());
        let module = crate::module(&db, file);
        (db, file, module)
    }

    /// Find a NameId by its text. Panics if not found.
    fn find_name(module: &crate::Module, text: &str) -> NameId {
        module
            .names()
            .find(|(_, n)| n.text == text)
            .unwrap_or_else(|| panic!("name {text:?} not found"))
            .0
    }

    /// Find the ExprId of the first `Expr::Reference` whose name string
    /// matches `text`.
    fn find_ref_expr(module: &crate::Module, text: &str) -> ExprId {
        module
            .exprs()
            .find(|(_, e)| matches!(e, crate::Expr::Reference(n) if n == text))
            .unwrap_or_else(|| panic!("reference to {text:?} not found"))
            .0
    }

    // ==================================================================
    // Existing tests
    // ==================================================================

    #[test]
    fn refs_to_returns_all_reference_sites() {
        // `let x = 1; in x + x` — x has two references after `in`.
        let (db, file, module) = setup("let x = 1; in x + x");
        let name_res = name_resolution(&db, file);

        let x_name = find_name(&module, "x");
        let refs = name_res.refs_to(x_name);
        assert_eq!(
            refs.len(),
            2,
            "x should have exactly 2 reference sites, got: {refs:?}"
        );
    }

    #[test]
    fn module_indices_binding_expr() {
        let (db, file, module) = setup("let x = 1 + 2; in x");
        let indices = crate::module_indices(&db, file);

        let x_name = find_name(&module, "x");
        assert!(
            indices.binding_expr.contains_key(&x_name),
            "x should have a binding expression in the index"
        );
        // Verify the value is an actual expression (not just key presence).
        let expr_id = indices.binding_expr[&x_name];
        assert!(
            matches!(module[expr_id], crate::Expr::BinOp { .. }),
            "binding expression for x should be the `1 + 2` BinOp"
        );
    }

    #[test]
    fn module_indices_param_to_lambda() {
        let (db, file, module) = setup("x: x + 1");
        let indices = crate::module_indices(&db, file);

        let x_name = find_name(&module, "x");
        let lambda_id = indices.param_to_lambda.get(&x_name);
        assert!(
            lambda_id.is_some(),
            "lambda param x should map to its owning Lambda"
        );
        assert!(
            matches!(module[*lambda_id.unwrap()], crate::Expr::Lambda { .. }),
            "param_to_lambda should point to a Lambda expression"
        );
    }

    #[test]
    fn global_builtin_names_all_resolve() {
        for name in super::GLOBAL_BUILTIN_NAMES {
            assert!(
                super::lookup_global_builtin(name).is_some(),
                "GLOBAL_BUILTIN_NAMES entry {name:?} should resolve via lookup_global_builtin"
            );
        }
    }

    // ==================================================================
    // Name resolution — scope & shadowing
    // ==================================================================

    #[test]
    fn shadow_inner_let_wins() {
        // Inner `x` shadows outer `x`. The reference after `in` resolves
        // to the inner binding.
        let (db, file, module) = setup("let x = 1; in let x = 2; in x");
        let name_res = name_resolution(&db, file);

        // There are two NameIds for "x" — find the inner one (it has LetIn
        // kind and is the second in iteration order).
        let x_names: Vec<NameId> = module
            .names()
            .filter(|(_, n)| n.text == "x")
            .map(|(id, _)| id)
            .collect();
        assert_eq!(x_names.len(), 2, "should have two 'x' names");

        let ref_expr = find_ref_expr(&module, "x");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        // The reference should resolve to one of the two x's.
        // The inner (shadowing) one is the second NameId allocated.
        let inner_x = x_names[1];
        assert_eq!(
            *resolved,
            ResolveResult::Definition(inner_x),
            "should resolve to the inner (shadowing) x"
        );
    }

    #[test]
    fn with_expr_resolution() {
        // `with` makes attrset fields available; unresolved names resolve
        // as WithExprs pointing at the with-expression.
        let (db, file, module) = setup("with { x = 1; }; x");
        let name_res = name_resolution(&db, file);

        let ref_expr = find_ref_expr(&module, "x");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        assert!(
            matches!(resolved, ResolveResult::WithExprs(..)),
            "x should resolve as WithExprs, got: {resolved:?}"
        );
    }

    #[test]
    fn local_shadows_with() {
        // A local let binding takes priority over `with`.
        let (db, file, module) = setup("let x = 1; in with { x = 2; }; x");
        let name_res = name_resolution(&db, file);

        let ref_expr = find_ref_expr(&module, "x");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        assert!(
            matches!(resolved, ResolveResult::Definition(_)),
            "x should resolve as Definition (local shadows with), got: {resolved:?}"
        );
    }

    #[test]
    fn nested_with_fallback() {
        // Two nested `with` scopes. `x` is only in the outer one, so
        // both with-exprs are recorded (inner first, outer as fallback).
        let (db, file, module) = setup("with { x = 1; }; with { y = 2; }; x");
        let name_res = name_resolution(&db, file);

        let ref_expr = find_ref_expr(&module, "x");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        match resolved {
            ResolveResult::WithExprs(inner, fallbacks) => {
                // Inner with is listed first, outer in fallbacks.
                assert!(
                    !fallbacks.is_empty(),
                    "should have fallback with-exprs, inner={inner:?}"
                );
            }
            other => panic!("expected WithExprs, got: {other:?}"),
        }
    }

    #[test]
    fn builtin_resolution() {
        // Builtin names resolve as Builtin, not Definition or WithExprs.
        let (db, file, module) = setup("toString 42");
        let name_res = name_resolution(&db, file);

        let ref_expr = find_ref_expr(&module, "toString");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        assert_eq!(
            *resolved,
            ResolveResult::Builtin("toString"),
            "toString should resolve as a builtin"
        );
    }

    #[test]
    fn unresolved_name_is_none() {
        // A bare name with no binding, no `with`, and not a builtin
        // resolves as None.
        let (db, file, module) = setup("nonexistent_var");
        let name_res = name_resolution(&db, file);

        let ref_expr = find_ref_expr(&module, "nonexistent_var");
        assert!(
            name_res.get(ref_expr).is_none(),
            "unresolved name should return None"
        );
    }

    #[test]
    fn lambda_params_in_scope() {
        // Both lambda parameters are visible in the body and resolve
        // to their respective NameIds.
        let (db, file, module) = setup("x: y: x");
        let name_res = name_resolution(&db, file);

        let x_name = find_name(&module, "x");
        let ref_expr = find_ref_expr(&module, "x");
        let resolved = name_res.get(ref_expr).expect("reference should resolve");
        assert_eq!(
            *resolved,
            ResolveResult::Definition(x_name),
            "reference to x should resolve to x's param NameId"
        );
    }

    #[test]
    fn inherit_resolves_in_parent_scope() {
        // `inherit x` inside an attrset creates a reference that resolves
        // to the outer let-binding's `x`.
        let (db, file, module) = setup("let x = 1; in { inherit x; }");
        let name_res = name_resolution(&db, file);

        let x_name = find_name(&module, "x");
        // The inherit creates a Reference expression for `x` — find it.
        // There should be exactly one reference expression.
        let ref_exprs: Vec<ExprId> = module
            .exprs()
            .filter(|(_, e)| matches!(e, crate::Expr::Reference(n) if n == "x"))
            .map(|(id, _)| id)
            .collect();
        assert!(
            !ref_exprs.is_empty(),
            "inherit should produce a Reference expr"
        );
        let resolved = name_res
            .get(ref_exprs[0])
            .expect("inherit reference should resolve");
        assert_eq!(
            *resolved,
            ResolveResult::Definition(x_name),
            "inherit x should resolve to the outer let-binding"
        );
    }

    // ==================================================================
    // SCC grouping
    // ==================================================================

    #[test]
    fn scc_mutual_recursion() {
        // f and g reference each other — they should be in the same SCC.
        let (db, file, module) = setup("let f = x: g x; g = x: f x; in f");
        let groups = group_def(&db, file);

        let f_name = find_name(&module, "f");
        let g_name = find_name(&module, "g");

        // Find the group containing f.
        let fg_group = groups
            .iter()
            .find(|g| g.iter().any(|td| td.name() == f_name))
            .expect("f should appear in some SCC group");

        // g should be in the same group.
        assert!(
            fg_group.iter().any(|td| td.name() == g_name),
            "f and g should be in the same SCC group"
        );
        assert_eq!(fg_group.len(), 2, "group should have exactly f and g");
    }

    #[test]
    fn scc_independent_bindings() {
        // a and b don't reference each other — separate SCCs.
        let (db, file, module) = setup("let a = 1; b = 2; in a + b");
        let groups = group_def(&db, file);

        let a_name = find_name(&module, "a");
        let b_name = find_name(&module, "b");

        let a_group = groups
            .iter()
            .find(|g| g.iter().any(|td| td.name() == a_name))
            .expect("a should appear in some SCC group");
        let b_group = groups
            .iter()
            .find(|g| g.iter().any(|td| td.name() == b_name))
            .expect("b should appear in some SCC group");

        assert_eq!(a_group.len(), 1, "a should be in its own group");
        assert_eq!(b_group.len(), 1, "b should be in its own group");
        // Verify they're different groups by checking names don't overlap.
        assert_ne!(a_group[0].name(), b_group[0].name());
    }

    #[test]
    fn scc_self_recursive() {
        // f references itself — it should be in a group by itself.
        let (db, file, module) = setup("let f = x: f (x + 1); in f");
        let groups = group_def(&db, file);

        let f_name = find_name(&module, "f");
        let f_group = groups
            .iter()
            .find(|g| g.iter().any(|td| td.name() == f_name))
            .expect("f should appear in some SCC group");

        assert_eq!(
            f_group.len(),
            1,
            "self-recursive f should be alone in its group"
        );
        // Lambda param `x` should NOT appear in any group.
        let x_in_groups = groups
            .iter()
            .flat_map(|g| g.iter())
            .any(|td| module[td.name()].text == "x");
        assert!(
            !x_in_groups,
            "lambda param x should not appear in SCC groups"
        );
    }

    #[test]
    fn scc_chain_dependency() {
        // a = 1; b = a; c = b; — linear chain, each in its own SCC,
        // topologically ordered so a comes before b comes before c.
        let (db, file, module) = setup("let a = 1; b = a; c = b; in c");
        let groups = group_def(&db, file);

        let a_name = find_name(&module, "a");
        let b_name = find_name(&module, "b");
        let c_name = find_name(&module, "c");

        // Each should be in its own group.
        assert!(
            groups.iter().all(|g| g.len() == 1),
            "all groups should have exactly 1 member for a linear chain"
        );

        // Find the position of each name in the group ordering.
        let pos_of = |name: NameId| -> usize {
            groups
                .iter()
                .position(|g| g[0].name() == name)
                .unwrap_or_else(|| panic!("name not found in groups"))
        };
        let a_pos = pos_of(a_name);
        let b_pos = pos_of(b_name);
        let c_pos = pos_of(c_name);

        assert!(
            a_pos < b_pos && b_pos < c_pos,
            "topological order should be a < b < c, got: a={a_pos}, b={b_pos}, c={c_pos}"
        );
    }
}
