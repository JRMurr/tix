pub mod aliases;
mod builtins;
pub(crate) mod collect;
mod constrain;
pub mod imports;
mod infer;
pub(crate) mod infer_expr;
pub(crate) mod storage;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod pbt;

use aliases::TypeAliasRegistry;
use comment_parser::{parse_and_collect, ParsedTy, TypeVarValue};
use derive_more::Debug;
use infer_expr::{PendingMerge, PendingOverload};
use lang_ast::{AstDb, ExprId, Module, NameId, NameResolution, NixFile, OverloadBinOp};
use lang_ty::{OutputTy, PrimitiveTy, Ty};
use std::collections::{HashMap, HashSet};
use storage::TypeStorage;
use thiserror::Error;

#[salsa::tracked]
pub fn check_file(db: &dyn AstDb, file: NixFile) -> Result<InferenceResult, LocatedError> {
    check_file_with_aliases(db, file, &TypeAliasRegistry::default())
}

/// Type-check a file with a pre-loaded type alias registry from .tix stubs.
/// Not a Salsa tracked function because `TypeAliasRegistry` is not Salsa-managed.
pub fn check_file_with_aliases(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
) -> Result<InferenceResult, LocatedError> {
    check_file_with_imports(db, file, aliases, HashMap::new())
}

/// Type-check a file with pre-loaded aliases and pre-resolved import types.
pub fn check_file_with_imports(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
    import_types: HashMap<ExprId, OutputTy>,
) -> Result<InferenceResult, LocatedError> {
    let module = lang_ast::module(db, file);
    let name_res = lang_ast::name_resolution(db, file);
    let grouped_defs = lang_ast::group_def(db, file);
    let check = CheckCtx::new(&module, &name_res, aliases.clone(), import_types);
    check.infer_prog(grouped_defs)
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
#[debug("TyId({_0:?})")]
pub struct TyId(u32);

impl From<u32> for TyId {
    #[inline]
    fn from(value: u32) -> Self {
        TyId(value)
    }
}

impl From<&u32> for TyId {
    #[inline]
    fn from(value: &u32) -> Self {
        TyId(*value)
    }
}

impl From<usize> for TyId {
    #[inline]
    fn from(value: usize) -> Self {
        u32::try_from(value).expect("TyId overflow").into()
    }
}

impl From<TyId> for usize {
    #[inline]
    fn from(value: TyId) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    pub name_ty_map: HashMap<NameId, OutputTy>,
    pub expr_ty_map: HashMap<ExprId, OutputTy>,
    pub warnings: Vec<LocatedWarning>,
}

impl InferenceResult {
    pub fn ty_for_name(&self, name: NameId) -> Option<OutputTy> {
        self.name_ty_map.get(&name).cloned()
    }

    pub fn ty_for_expr(&self, expr: ExprId) -> Option<OutputTy> {
        self.expr_ty_map.get(&expr).cloned()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum InferenceError {
    #[error("Type mismatch: {0:?} is not a subtype of {1:?}")]
    TypeMismatch(Ty<TyId>, Ty<TyId>),

    #[error("Missing field: {0:?}")]
    MissingField(smol_str::SmolStr),

    #[error("Can not do binary operation ({1:?}) ({0:?}) ({2:?})")]
    InvalidBinOp(OverloadBinOp, Ty<TyId>, Ty<TyId>),

    #[error("Can not do attrset merge on ({0:?}) ({1:?})")]
    InvalidAttrMerge(Ty<TyId>, Ty<TyId>),
}

/// An inference error paired with the expression where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocatedError {
    pub error: InferenceError,
    /// The expression that was being inferred when the error occurred.
    pub at_expr: ExprId,
}

impl std::fmt::Display for LocatedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl std::error::Error for LocatedError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Warning {
    UnresolvedName(smol_str::SmolStr),
}

impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::UnresolvedName(name) => write!(f, "Unresolved name: {name}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocatedWarning {
    pub warning: Warning,
    pub at_expr: ExprId,
}

/// Partial inference results plus all collected errors.
/// Allows the LSP to report diagnostics even when inference fails partway.
#[derive(Debug, Clone)]
pub struct CheckResult {
    /// If inference succeeded, contains the full result. If it failed, this is
    /// None (future: partial results from error recovery).
    pub inference: Option<InferenceResult>,
    pub errors: Vec<LocatedError>,
    pub warnings: Vec<LocatedWarning>,
}

/// Type-check a file, collecting errors instead of aborting on the first one.
/// Returns partial results when possible.
pub fn check_file_collecting(
    db: &dyn AstDb,
    file: NixFile,
    aliases: &TypeAliasRegistry,
    import_types: HashMap<ExprId, OutputTy>,
) -> CheckResult {
    match check_file_with_imports(db, file, aliases, import_types) {
        Ok(inference) => {
            let warnings = inference.warnings.clone();
            CheckResult {
                inference: Some(inference),
                errors: Vec::new(),
                warnings,
            }
        }
        Err(located) => CheckResult {
            inference: None,
            errors: vec![located],
            // Warnings accumulated before the error are lost. Acceptable
            // until error recovery is added.
            warnings: Vec::new(),
        },
    }
}

#[derive(Debug, Clone)]
pub struct CheckCtx<'db> {
    module: &'db Module,
    name_res: &'db NameResolution,

    /// The expression currently being inferred. Updated at the top of
    /// `infer_expr` so that errors from `constrain()` or sub-calls are
    /// attributed to the correct source location.
    current_expr: ExprId,

    /// Warnings accumulated during inference (e.g. unresolved names).
    warnings: Vec<LocatedWarning>,

    table: TypeStorage,

    /// Maps generalized names to their polymorphic TyId.
    /// The TyId + variable levels encode the polymorphic scheme.
    poly_type_env: HashMap<NameId, TyId>,

    /// Cache (sub, sup) pairs already processed by constrain() to avoid cycles.
    /// Intentionally never cleared between SCC groups: extrusion creates fresh
    /// vars linked to old ones via constrain(), and re-processing those pairs
    /// would cause infinite loops across extrusion boundaries. The cache is
    /// scoped to the lifetime of this CheckCtx (one per file), so it doesn't
    /// grow across files.
    constrain_cache: HashSet<(TyId, TyId)>,

    /// Primitive type cache for deduplication.
    prim_cache: HashMap<PrimitiveTy, TyId>,

    /// Pending overloaded binary op constraints to resolve later.
    pending_overloads: Vec<PendingOverload>,

    /// Pending attrset merge constraints to resolve later.
    pending_merges: Vec<PendingMerge>,

    /// Overloads that couldn't be resolved in their SCC group and should be
    /// re-instantiated per call-site during extrusion.
    /// Maps from operand TyId → list of deferred overloads referencing that var.
    deferred_overloads: Vec<PendingOverload>,

    /// Early-canonicalized types for names, captured at generalization time
    /// before use-site extrusions contaminate polymorphic variables with
    /// concrete bounds.
    early_canonical: HashMap<NameId, OutputTy>,

    /// Type alias registry loaded from .tix declaration files.
    type_aliases: TypeAliasRegistry,

    /// Pre-computed types for resolved import expressions. When an Apply ExprId
    /// is in this map, its type comes from the imported file's root expression
    /// rather than from the generic `import :: a -> b` builtin signature.
    import_types: HashMap<ExprId, OutputTy>,
}

impl<'db> CheckCtx<'db> {
    pub fn new(
        module: &'db Module,
        name_res: &'db NameResolution,
        type_aliases: TypeAliasRegistry,
        import_types: HashMap<ExprId, OutputTy>,
    ) -> Self {
        Self {
            module,
            name_res,
            current_expr: module.entry_expr,
            warnings: Vec::new(),
            table: TypeStorage::new(),
            poly_type_env: HashMap::new(),
            constrain_cache: HashSet::new(),
            prim_cache: HashMap::new(),
            pending_overloads: Vec::new(),
            pending_merges: Vec::new(),
            deferred_overloads: Vec::new(),
            early_canonical: HashMap::new(),
            type_aliases,
            import_types,
        }
    }

    /// Allocate a fresh type variable at the current level.
    fn new_var(&mut self) -> TyId {
        self.table.new_var()
    }

    /// Allocate a concrete type and return its TyId.
    fn alloc_concrete(&mut self, ty: Ty<TyId>) -> TyId {
        self.table.new_concrete(ty)
    }

    /// Allocate a primitive type, deduplicating via cache.
    fn alloc_prim(&mut self, prim: PrimitiveTy) -> TyId {
        if let Some(&id) = self.prim_cache.get(&prim) {
            return id;
        }
        let id = self.alloc_concrete(Ty::Primitive(prim));
        self.prim_cache.insert(prim, id);
        id
    }

    /// Get the pre-allocated TyId for a name (used during inference of the name's
    /// own definition, before it has been generalized).
    fn ty_for_name_direct(&self, name: NameId) -> TyId {
        let id: TyId = u32::from(name.into_raw()).into();
        debug_assert!(
            usize::from(id) < self.table.len(),
            "ty_for_name_direct: TyId {id:?} out of bounds (storage has {} entries)",
            self.table.len()
        );
        id
    }

    /// Get the pre-allocated TyId for an expression.
    fn ty_for_expr(&self, i: ExprId) -> TyId {
        let idx = self.module.names().len() as u32 + u32::from(i.into_raw());
        let id: TyId = idx.into();
        debug_assert!(
            usize::from(id) < self.table.len(),
            "ty_for_expr: TyId {id:?} out of bounds (storage has {} entries)",
            self.table.len()
        );
        id
    }

    // ==========================================================================
    // Type annotation interning (doc comment → internal types)
    // ==========================================================================

    // ==========================================================================
    // OutputTy interning (import results → internal types)
    // ==========================================================================

    /// Intern an OutputTy into this file's TypeStorage, creating fresh TyIds.
    ///
    /// Each TyVar(n) in the OutputTy maps to a fresh variable (via a local
    /// HashMap). This ensures imported types are fully isolated from the
    /// source file's TypeStorage — constraints applied in this file cannot
    /// propagate back to the imported file.
    fn intern_output_ty(&mut self, ty: &OutputTy) -> TyId {
        let mut var_map: HashMap<u32, TyId> = HashMap::new();
        self.intern_output_ty_inner(ty, &mut var_map)
    }

    fn intern_output_ty_inner(
        &mut self,
        ty: &OutputTy,
        var_map: &mut HashMap<u32, TyId>,
    ) -> TyId {
        match ty {
            OutputTy::TyVar(n) => {
                *var_map.entry(*n).or_insert_with(|| self.new_var())
            }
            OutputTy::Primitive(prim) => self.alloc_prim(*prim),
            OutputTy::List(inner) => {
                let elem = self.intern_output_ty_inner(&inner.0, var_map);
                self.alloc_concrete(Ty::List(elem))
            }
            OutputTy::Lambda { param, body } => {
                let p = self.intern_output_ty_inner(&param.0, var_map);
                let b = self.intern_output_ty_inner(&body.0, var_map);
                self.alloc_concrete(Ty::Lambda { param: p, body: b })
            }
            OutputTy::AttrSet(attr) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let field_ty = self.intern_output_ty_inner(&v.0, var_map);
                    fields.insert(k.clone(), field_ty);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_output_ty_inner(&d.0, var_map));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                }))
            }
            // Union: create a fresh variable with each member as a lower bound.
            OutputTy::Union(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_output_ty_inner(&m.0, var_map);
                    self.constrain(member_ty, var)
                        .expect("union import constraint should not fail");
                }
                var
            }
            // Intersection: create a fresh variable with each member as an upper bound.
            OutputTy::Intersection(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_output_ty_inner(&m.0, var_map);
                    self.constrain(var, member_ty)
                        .expect("intersection import constraint should not fail");
                }
                var
            }
        }
    }

    /// If `name_id` has a doc comment type annotation (e.g. `/** type: x :: int */`),
    /// constrain `ty` to match the declared type. Returns Ok(()) if no annotation
    /// is present or if the constraint succeeds.
    fn apply_type_annotation(&mut self, name_id: NameId, ty: TyId) -> Result<(), LocatedError> {
        let type_annotation =
            self.module
                .type_dec_map
                .docs_for_name(name_id)
                .and_then(|docs| {
                    let parsed: Vec<_> = docs
                        .iter()
                        .flat_map(|doc| parse_and_collect(doc).unwrap_or_default())
                        .collect();
                    let name_str = &self.module[name_id].text;
                    parsed.into_iter().find_map(|decl| {
                        if decl.identifier == *name_str {
                            Some(decl.type_expr)
                        } else {
                            None
                        }
                    })
                });

        if let Some(known_ty) = type_annotation {
            let annotation_ty = self.intern_fresh_ty(known_ty);
            self.constrain(ty, annotation_ty)
                .map_err(|err| self.locate_err(err))?;
            self.constrain(annotation_ty, ty)
                .map_err(|err| self.locate_err(err))?;
        }

        Ok(())
    }

    /// Intern a ParsedTy with fresh type variables for each free generic var
    /// and alias resolution for Reference vars. Each call produces an independent
    /// "instance" — analogous to polymorphic instantiation.
    fn intern_fresh_ty(&mut self, ty: ParsedTy) -> TyId {
        let free_vars = ty.free_vars();

        let subs: HashMap<TypeVarValue, TyId> = free_vars
            .iter()
            .map(|var| {
                let ty_id = match var {
                    TypeVarValue::Generic(_) => self.new_var(),
                    TypeVarValue::Reference(ref_name) => {
                        // Resolve against loaded type aliases. If found,
                        // recursively intern the alias body (with its own
                        // fresh vars) to get a polymorphic instance.
                        if let Some(alias_body) = self.type_aliases.get(ref_name).cloned() {
                            self.intern_fresh_ty(alias_body)
                        } else {
                            // Unknown reference — degrade to fresh variable.
                            self.new_var()
                        }
                    }
                };
                (var.clone(), ty_id)
            })
            .collect();

        self.intern_parsed_ty(&ty, &subs)
    }

    fn intern_parsed_ty(
        &mut self,
        ty: &ParsedTy,
        substitutions: &HashMap<TypeVarValue, TyId>,
    ) -> TyId {
        match ty {
            ParsedTy::TyVar(var) => {
                let replacement = substitutions
                    .get(var)
                    .unwrap_or_else(|| panic!("No replacement for {var:?}"));
                *replacement
            }
            ParsedTy::Primitive(prim) => self.alloc_prim(*prim),
            ParsedTy::List(inner) => {
                let new_inner = self.intern_parsed_ty(&inner.0, substitutions);
                self.alloc_concrete(Ty::List(new_inner))
            }
            ParsedTy::Lambda { param, body } => {
                let new_param = self.intern_parsed_ty(&param.0, substitutions);
                let new_body = self.intern_parsed_ty(&body.0, substitutions);
                self.alloc_concrete(Ty::Lambda {
                    param: new_param,
                    body: new_body,
                })
            }
            ParsedTy::AttrSet(attr) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in &attr.fields {
                    let new_v = self.intern_parsed_ty(&v.0, substitutions);
                    fields.insert(k.clone(), new_v);
                }
                let dyn_ty = attr
                    .dyn_ty
                    .as_ref()
                    .map(|d| self.intern_parsed_ty(&d.0, substitutions));
                self.alloc_concrete(Ty::AttrSet(lang_ty::AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                }))
            }
            // Union annotations: create a fresh variable with each member as a lower bound.
            // This encodes `int | string` as a var where `int <: var` and `string <: var`.
            ParsedTy::Union(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(member_ty, var)
                        .expect("union annotation constraint should not fail");
                }
                var
            }
            // Intersection annotations: create a fresh variable with each member as an upper bound.
            // This encodes `a & b` as a var where `var <: a` and `var <: b`.
            ParsedTy::Intersection(members) => {
                let var = self.new_var();
                for m in members {
                    let member_ty = self.intern_parsed_ty(&m.0, substitutions);
                    self.constrain(var, member_ty)
                        .expect("intersection annotation constraint should not fail");
                }
                var
            }
        }
    }

    /// Wrap a bare `InferenceError` with the current expression location.
    fn locate_err(&self, err: InferenceError) -> LocatedError {
        LocatedError {
            error: err,
            at_expr: self.current_expr,
        }
    }

    /// Record a warning at the current expression.
    fn emit_warning(&mut self, warning: Warning) {
        self.warnings.push(LocatedWarning {
            warning,
            at_expr: self.current_expr,
        });
    }
}
