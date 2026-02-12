// ==============================================================================
// Polarity-Aware Canonicalization
// ==============================================================================
//
// Converts internal TyId representation to canonical OutputTy.
// Variables are expanded based on polarity:
// - Positive position (output): variable → union of lower bounds
// - Negative position (input): variable → intersection of upper bounds
// Lambda params flip polarity.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{CheckCtx, InferenceResult, TyId};
use crate::storage::{TypeEntry, TypeStorage};
use lang_ty::{AttrSetTy, OutputTy, Ty, TyRef};

// ==============================================================================
// Standalone canonicalization — can be called during inference (before Collector
// takes ownership of CheckCtx) to snapshot a type's canonical form while bounds
// are still clean (pre-extrusion).
// ==============================================================================

struct StandaloneCanon<'a> {
    table: &'a TypeStorage,
    cache: HashMap<(TyId, bool), OutputTy>,
    in_progress: HashSet<(TyId, bool)>,
}

impl<'a> StandaloneCanon<'a> {
    fn new(table: &'a TypeStorage) -> Self {
        Self {
            table,
            cache: HashMap::new(),
            in_progress: HashSet::new(),
        }
    }

    fn canonicalize(&mut self, ty_id: TyId, positive: bool) -> OutputTy {
        let key = (ty_id, positive);

        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }

        if self.in_progress.contains(&key) {
            return OutputTy::TyVar(ty_id.0);
        }

        self.in_progress.insert(key);
        let result = self.canonicalize_inner(ty_id, positive);
        self.in_progress.remove(&key);

        self.cache.insert(key, result.clone());
        result
    }

    fn canonicalize_inner(&mut self, ty_id: TyId, positive: bool) -> OutputTy {
        let entry = self.table.get(ty_id).clone();

        match entry {
            TypeEntry::Variable(v) => {
                if positive {
                    self.expand_bounds_as_union(&v.lower_bounds, ty_id)
                } else {
                    self.expand_bounds_as_intersection(&v.upper_bounds, ty_id)
                }
            }
            TypeEntry::Concrete(ty) => self.canonicalize_concrete(&ty, positive),
        }
    }

    fn expand_bounds_as_union(&mut self, bounds: &[TyId], var_id: TyId) -> OutputTy {
        let bounds = bounds.to_vec();
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, true))
            .collect();

        let flattened = flatten_union(members);

        let concrete: Vec<OutputTy> = flattened
            .into_iter()
            .filter(|m| !matches!(m, OutputTy::TyVar(_)))
            .collect();

        match concrete.len() {
            0 => OutputTy::TyVar(var_id.0),
            1 => concrete.into_iter().next().unwrap(),
            _ => OutputTy::Union(concrete.into_iter().map(TyRef::from).collect()),
        }
    }

    fn expand_bounds_as_intersection(&mut self, bounds: &[TyId], var_id: TyId) -> OutputTy {
        let bounds = bounds.to_vec();
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, false))
            .collect();

        let flattened = flatten_intersection(members);

        let concrete: Vec<OutputTy> = flattened
            .into_iter()
            .filter(|m| !matches!(m, OutputTy::TyVar(_)))
            .collect();

        let concrete = merge_attrset_intersection(concrete);

        match concrete.len() {
            0 => OutputTy::TyVar(var_id.0),
            1 => concrete.into_iter().next().unwrap(),
            _ => OutputTy::Intersection(concrete.into_iter().map(TyRef::from).collect()),
        }
    }

    fn canonicalize_concrete(&mut self, ty: &Ty<TyId>, positive: bool) -> OutputTy {
        match ty {
            Ty::Primitive(p) => OutputTy::Primitive(*p),
            Ty::TyVar(x) => OutputTy::TyVar(*x),
            Ty::List(elem) => {
                let c_elem = self.canonicalize(*elem, positive);
                OutputTy::List(TyRef::from(c_elem))
            }
            Ty::Lambda { param, body } => {
                let c_param = self.canonicalize(*param, !positive);
                let c_body = self.canonicalize(*body, positive);
                OutputTy::Lambda {
                    param: TyRef::from(c_param),
                    body: TyRef::from(c_body),
                }
            }
            Ty::AttrSet(attr) => {
                let mut new_fields = BTreeMap::new();
                for (k, &v) in &attr.fields {
                    let c_field = self.canonicalize(v, positive);
                    new_fields.insert(k.clone(), TyRef::from(c_field));
                }
                let dyn_ty = attr
                    .dyn_ty
                    .map(|d| TyRef::from(self.canonicalize(d, positive)));
                OutputTy::AttrSet(AttrSetTy {
                    fields: new_fields,
                    dyn_ty,
                    open: attr.open,
                })
            }
        }
    }
}

/// Canonicalize a TyId into an OutputTy using only a TypeStorage reference.
/// This captures the type's canonical form at the current moment — before
/// use-site extrusions add concrete bounds back onto polymorphic variables.
pub fn canonicalize_standalone(table: &TypeStorage, ty_id: TyId, positive: bool) -> OutputTy {
    let mut canon = StandaloneCanon::new(table);
    canon.canonicalize(ty_id, positive)
}

// ==============================================================================
// Shared helpers — used by both StandaloneCanon and Collector
// ==============================================================================

/// Flatten nested unions and deduplicate members.
/// Uses structural normalization so that types differing only in TyVar IDs
/// (e.g. two extrusions of the same polymorphic type) are recognized as duplicates.
fn flatten_union(members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for m in members {
        match m {
            OutputTy::Union(inner) => {
                for sub in inner {
                    let sub_ty = (*sub.0).clone();
                    if seen.insert(sub_ty.normalize_vars()) {
                        result.push(sub_ty);
                    }
                }
            }
            other => {
                if seen.insert(other.normalize_vars()) {
                    result.push(other);
                }
            }
        }
    }
    result
}

/// Flatten nested intersections and deduplicate members.
/// Uses structural normalization so that types differing only in TyVar IDs
/// are recognized as duplicates.
fn flatten_intersection(members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for m in members {
        match m {
            OutputTy::Intersection(inner) => {
                for sub in inner {
                    let sub_ty = (*sub.0).clone();
                    if seen.insert(sub_ty.normalize_vars()) {
                        result.push(sub_ty);
                    }
                }
            }
            other => {
                if seen.insert(other.normalize_vars()) {
                    result.push(other);
                }
            }
        }
    }
    result
}

/// Merge multiple attrsets in an intersection into a single attrset.
/// The intersection of `{ foo: int }` and `{ bar: string }` is `{ foo: int, bar: string }`.
/// For overlapping fields, the field types are intersected.
fn merge_attrset_intersection(members: Vec<OutputTy>) -> Vec<OutputTy> {
    let mut attrsets: Vec<AttrSetTy<TyRef>> = Vec::new();
    let mut others: Vec<OutputTy> = Vec::new();

    for m in members {
        match m {
            OutputTy::AttrSet(attr) => attrsets.push(attr),
            other => others.push(other),
        }
    }

    if attrsets.is_empty() {
        return others;
    }

    // Merge all attrsets. For overlapping fields, take the most specific
    // (for now, just take the non-TyVar one; a proper implementation would
    // intersect field types).
    let mut merged_fields: BTreeMap<smol_str::SmolStr, TyRef> = BTreeMap::new();
    let mut any_open = false;

    for attr in &attrsets {
        any_open = any_open || attr.open;
        for (k, v) in &attr.fields {
            merged_fields
                .entry(k.clone())
                .and_modify(|existing| {
                    // If the existing type is a TyVar and the new one isn't, prefer the new one.
                    // If both are concrete and equal, keep either. Otherwise keep existing.
                    // TODO: proper intersection of field types.
                    if matches!(&*existing.0, OutputTy::TyVar(_)) {
                        *existing = v.clone();
                    }
                })
                .or_insert_with(|| v.clone());
        }
    }

    let merged = OutputTy::AttrSet(AttrSetTy {
        fields: merged_fields,
        dyn_ty: None, // TODO: merge dyn_tys
        open: any_open,
    });

    others.push(merged);
    others
}

// ==============================================================================
// Collector — final canonicalization pass (after all inference is complete)
// ==============================================================================

pub struct Collector<'db> {
    /// Cache keyed by (TyId, polarity).
    cache: HashMap<(TyId, bool), OutputTy>,
    /// Track which TyIds are currently being expanded (cycle detection).
    in_progress: HashSet<(TyId, bool)>,
    pub(crate) ctx: CheckCtx<'db>,
}

impl<'db> Collector<'db> {
    pub fn new(ctx: CheckCtx<'db>) -> Self {
        Self {
            cache: HashMap::new(),
            in_progress: HashSet::new(),
            ctx,
        }
    }

    pub fn finalize_inference(&mut self) -> InferenceResult {
        let name_tys: Vec<_> = self
            .ctx
            .module
            .names()
            .map(|(name, _)| {
                let ty: TyId = (u32::from(name.into_raw())).into();
                (name, ty)
            })
            .collect();

        let expr_tys: Vec<_> = self
            .ctx
            .module
            .exprs()
            .map(|(expr, _)| {
                let ty = self.ctx.ty_for_expr(expr);
                (expr, ty)
            })
            .collect();

        let name_cnt = self.ctx.module.names().len();
        let expr_cnt = self.ctx.module.exprs().len();
        let mut name_ty_map = HashMap::with_capacity(name_cnt);
        let mut expr_ty_map = HashMap::with_capacity(expr_cnt);

        for (name, ty) in name_tys {
            // Prefer the early-canonicalized type (captured before use-site
            // extrusion contaminated the bounds) over late canonicalization.
            let output = if let Some(early) = self.ctx.early_canonical.get(&name) {
                early.clone()
            } else {
                self.canonicalize(ty, true)
            };
            name_ty_map.insert(name, output.normalize_vars());
        }

        for (expr, ty) in expr_tys {
            let mut output = self.canonicalize(ty, true);
            if expr == self.ctx.module.entry_expr {
                output = output.normalize_vars();
            }
            expr_ty_map.insert(expr, output);
        }

        InferenceResult {
            name_ty_map,
            expr_ty_map,
        }
    }

    /// Canonicalize a TyId into an OutputTy, expanding variables based on polarity.
    fn canonicalize(&mut self, ty_id: TyId, positive: bool) -> OutputTy {
        let key = (ty_id, positive);

        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }

        // Cycle detection.
        if self.in_progress.contains(&key) {
            return OutputTy::TyVar(ty_id.0);
        }

        self.in_progress.insert(key);
        let result = self.canonicalize_inner(ty_id, positive);
        self.in_progress.remove(&key);

        self.cache.insert(key, result.clone());
        result
    }

    fn canonicalize_inner(&mut self, ty_id: TyId, positive: bool) -> OutputTy {
        let entry = self.ctx.table.get(ty_id).clone();

        match entry {
            TypeEntry::Variable(v) => {
                if positive {
                    self.expand_bounds_as_union(&v.lower_bounds, ty_id)
                } else {
                    self.expand_bounds_as_intersection(&v.upper_bounds, ty_id)
                }
            }
            TypeEntry::Concrete(ty) => self.canonicalize_concrete(&ty, positive),
        }
    }

    /// Expand lower bounds of a variable into a union (positive position).
    fn expand_bounds_as_union(&mut self, bounds: &[TyId], var_id: TyId) -> OutputTy {
        let bounds = bounds.to_vec();
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, true))
            .collect();

        let flattened = flatten_union(members);

        // Filter out bare type variables — in positive position, a TyVar bound
        // means "something unknown flows in" which adds no information to a union.
        let concrete: Vec<OutputTy> = flattened
            .into_iter()
            .filter(|m| !matches!(m, OutputTy::TyVar(_)))
            .collect();

        match concrete.len() {
            0 => OutputTy::TyVar(var_id.0),
            1 => concrete.into_iter().next().unwrap(),
            _ => OutputTy::Union(concrete.into_iter().map(TyRef::from).collect()),
        }
    }

    /// Expand upper bounds of a variable into an intersection (negative position).
    fn expand_bounds_as_intersection(&mut self, bounds: &[TyId], var_id: TyId) -> OutputTy {
        let bounds = bounds.to_vec();
        let members: Vec<OutputTy> = bounds
            .iter()
            .map(|&b| self.canonicalize(b, false))
            .collect();

        let flattened = flatten_intersection(members);

        // Filter out bare type variables — in negative position, a TyVar bound
        // means "flows into something unknown" which adds no information.
        let concrete: Vec<OutputTy> = flattened
            .into_iter()
            .filter(|m| !matches!(m, OutputTy::TyVar(_)))
            .collect();

        // Merge multiple attrsets into one (intersection of records = record with all fields).
        let concrete = merge_attrset_intersection(concrete);

        match concrete.len() {
            0 => OutputTy::TyVar(var_id.0),
            1 => concrete.into_iter().next().unwrap(),
            _ => OutputTy::Intersection(concrete.into_iter().map(TyRef::from).collect()),
        }
    }

    fn canonicalize_concrete(&mut self, ty: &Ty<TyId>, positive: bool) -> OutputTy {
        match ty {
            Ty::Primitive(p) => OutputTy::Primitive(*p),
            Ty::TyVar(x) => OutputTy::TyVar(*x),
            Ty::List(elem) => {
                let c_elem = self.canonicalize(*elem, positive);
                OutputTy::List(TyRef::from(c_elem))
            }
            Ty::Lambda { param, body } => {
                let c_param = self.canonicalize(*param, !positive);
                let c_body = self.canonicalize(*body, positive);
                OutputTy::Lambda {
                    param: TyRef::from(c_param),
                    body: TyRef::from(c_body),
                }
            }
            Ty::AttrSet(attr) => {
                let mut new_fields = BTreeMap::new();
                for (k, &v) in &attr.fields {
                    let c_field = self.canonicalize(v, positive);
                    new_fields.insert(k.clone(), TyRef::from(c_field));
                }
                let dyn_ty = attr
                    .dyn_ty
                    .map(|d| TyRef::from(self.canonicalize(d, positive)));
                OutputTy::AttrSet(AttrSetTy {
                    fields: new_fields,
                    dyn_ty,
                    open: attr.open,
                })
            }
        }
    }
}
