use std::fmt;
use std::sync::Arc;

use derive_more::Debug;
use rustc_hash::FxHashMap;

use crate::{AttrSetTy, PrimitiveTy};

// ==============================================================================
// OutputTy — the canonical output representation of types
// ==============================================================================
//
// During inference we use `Ty<TyId>` which has 5 variants (no unions/intersections).
// After inference, canonicalization produces `OutputTy` which adds Union and Intersection.
// This separation makes it impossible to accidentally construct a union during inference.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OutputTy {
    #[debug("TyVar({_0:?})")]
    TyVar(u32),

    #[debug("{_0:?}")]
    Primitive(PrimitiveTy),

    #[debug("List({_0:?})")]
    List(TyRef),

    #[debug("Lambda({param:?} -> {body:?})")]
    Lambda { param: TyRef, body: TyRef },

    #[debug("{_0:?}")]
    AttrSet(AttrSetTy<TyRef>),

    /// A union of types (e.g. `int | string`). Produced when different branches
    /// of if-then-else or list elements have different types.
    #[debug("Union({_0:?})")]
    Union(Vec<TyRef>),

    /// An intersection of types (e.g. `(int -> int) & (string -> string)`).
    /// Produced in negative/input positions when a variable has multiple upper bounds.
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<TyRef>),
}

/// Arc-wrapped OutputTy for recursive type structures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(pub Arc<OutputTy>);

/// The canonical output type. This is what InferenceResult maps names/exprs to.
pub type ArcTy = OutputTy;

impl From<OutputTy> for TyRef {
    fn from(value: OutputTy) -> Self {
        TyRef(Arc::new(value))
    }
}

pub type Substitutions = FxHashMap<u32, u32>;

// ==============================================================================
// Normalization and free variable collection on OutputTy
// ==============================================================================

impl OutputTy {
    /// Normalize all the ty vars to start from 0 instead
    /// of the "random" nums it has from solving.
    pub fn normalize_vars(&self) -> OutputTy {
        let free_vars = self.free_type_vars();

        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, i as u32))
            .collect();

        self.normalize_inner(&subs)
    }

    pub fn normalize_inner(&self, free: &Substitutions) -> OutputTy {
        match self {
            OutputTy::TyVar(x) => {
                let new_idx = free.get(x).unwrap();
                OutputTy::TyVar(*new_idx)
            }
            OutputTy::List(inner) => OutputTy::List(inner.0.normalize_inner(free).into()),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: param.0.normalize_inner(free).into(),
                body: body.0.normalize_inner(free).into(),
            },
            OutputTy::AttrSet(attr_set_ty) => OutputTy::AttrSet(attr_set_ty.normalize_inner(free)),
            OutputTy::Primitive(_) => self.clone(),
            OutputTy::Union(members) => OutputTy::Union(
                members
                    .iter()
                    .map(|m| m.0.normalize_inner(free).into())
                    .collect(),
            ),
            OutputTy::Intersection(members) => OutputTy::Intersection(
                members
                    .iter()
                    .map(|m| m.0.normalize_inner(free).into())
                    .collect(),
            ),
        }
    }

    /// Returns true if any Lambda in this type has a non-primitive param type.
    /// Such types can't be precisely generated in PBT because the `if param == <value>`
    /// code generation pattern doesn't fully constrain non-primitive params in
    /// SimpleSub's polarity-aware canonicalization.
    pub fn has_non_primitive_lambda_param(&self) -> bool {
        match self {
            OutputTy::Lambda { param, body } => {
                !matches!(&*param.0, OutputTy::Primitive(_) | OutputTy::TyVar(_))
                    || param.0.has_non_primitive_lambda_param()
                    || body.0.has_non_primitive_lambda_param()
            }
            OutputTy::List(inner) => inner.0.has_non_primitive_lambda_param(),
            OutputTy::AttrSet(attr) => {
                attr.fields
                    .values()
                    .any(|v| v.0.has_non_primitive_lambda_param())
                    || attr
                        .dyn_ty
                        .as_ref()
                        .is_some_and(|d| d.0.has_non_primitive_lambda_param())
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                members.iter().any(|m| m.0.has_non_primitive_lambda_param())
            }
            OutputTy::TyVar(_) | OutputTy::Primitive(_) => false,
        }
    }

    /// Returns true if this type or any of its children contains a Union or Intersection.
    pub fn contains_union_or_intersection(&self) -> bool {
        match self {
            OutputTy::Union(_) | OutputTy::Intersection(_) => true,
            OutputTy::TyVar(_) | OutputTy::Primitive(_) => false,
            OutputTy::List(inner) => inner.0.contains_union_or_intersection(),
            OutputTy::Lambda { param, body } => {
                param.0.contains_union_or_intersection() || body.0.contains_union_or_intersection()
            }
            OutputTy::AttrSet(attr) => {
                attr.fields
                    .values()
                    .any(|v| v.0.contains_union_or_intersection())
                    || attr
                        .dyn_ty
                        .as_ref()
                        .is_some_and(|d| d.0.contains_union_or_intersection())
            }
        }
    }

    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_free_type_vars(&mut result, &mut seen);
        result
    }

    fn collect_free_type_vars(
        &self,
        result: &mut Vec<u32>,
        seen: &mut std::collections::HashSet<u32>,
    ) {
        match self {
            OutputTy::TyVar(x) => {
                if seen.insert(*x) {
                    result.push(*x);
                }
            }
            OutputTy::List(inner) => inner.0.collect_free_type_vars(result, seen),
            OutputTy::Lambda { param, body } => {
                param.0.collect_free_type_vars(result, seen);
                body.0.collect_free_type_vars(result, seen);
            }
            OutputTy::AttrSet(attr_set_ty) => {
                for v in attr_set_ty.fields.values() {
                    v.0.collect_free_type_vars(result, seen);
                }
                if let Some(dyn_ty) = &attr_set_ty.dyn_ty {
                    dyn_ty.0.collect_free_type_vars(result, seen);
                }
            }
            OutputTy::Primitive(_) => {}
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for m in members {
                    m.0.collect_free_type_vars(result, seen);
                }
            }
        }
    }
}

// ==============================================================================
// Display — human-readable type printing
// ==============================================================================
//
// Type variables are rendered as lowercase letters (a, b, c, ..., z, a1, b1, ...).
// Operator precedence is handled by checking whether parentheses are needed:
//   `->` is right-associative and lowest precedence
//   `|` is next
//   `&` is next
//   atoms (primitives, lists, attrsets, type vars) are highest

/// Convert a type variable index to a letter-based name: 0→a, 1→b, ..., 25→z, 26→a1, ...
fn tyvar_name(idx: u32) -> String {
    let letter = (b'a' + (idx % 26) as u8) as char;
    let suffix = idx / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{letter}{suffix}")
    }
}

impl fmt::Display for OutputTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputTy::TyVar(x) => write!(f, "{}", tyvar_name(*x)),
            OutputTy::Primitive(p) => write!(f, "{p}"),
            OutputTy::List(inner) => write!(f, "[{inner}]"),
            OutputTy::Lambda { param, body } => {
                // Parenthesize the param if it's a lambda, union, or intersection
                // to avoid ambiguity (-> is right-associative).
                let needs_parens = matches!(
                    &*param.0,
                    OutputTy::Lambda { .. } | OutputTy::Union(_) | OutputTy::Intersection(_)
                );
                if needs_parens {
                    write!(f, "({param}) -> {body}")
                } else {
                    write!(f, "{param} -> {body}")
                }
            }
            OutputTy::AttrSet(attr) => write!(f, "{attr}"),
            OutputTy::Union(members) => {
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    // Parenthesize lambdas inside unions to avoid ambiguity.
                    let needs_parens = matches!(&*m.0, OutputTy::Lambda { .. });
                    if needs_parens {
                        write!(f, "({m})")?;
                    } else {
                        write!(f, "{m}")?;
                    }
                }
                Ok(())
            }
            OutputTy::Intersection(members) => {
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " & ")?;
                    }
                    // Parenthesize lambdas and unions inside intersections.
                    let needs_parens =
                        matches!(&*m.0, OutputTy::Lambda { .. } | OutputTy::Union(_));
                    if needs_parens {
                        write!(f, "({m})")?;
                    } else {
                        write!(f, "{m}")?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for TyRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&*self.0, f)
    }
}

impl fmt::Display for PrimitiveTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimitiveTy::Null => write!(f, "null"),
            PrimitiveTy::Bool => write!(f, "bool"),
            PrimitiveTy::Int => write!(f, "int"),
            PrimitiveTy::Float => write!(f, "float"),
            PrimitiveTy::String => write!(f, "string"),
            PrimitiveTy::Path => write!(f, "path"),
            PrimitiveTy::Uri => write!(f, "uri"),
        }
    }
}

impl fmt::Display for AttrSetTy<TyRef> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        for (i, (k, v)) in self.fields.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{k}: {v}")?;
        }
        if self.open {
            if !self.fields.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        write!(f, " }}")
    }
}

impl AttrSetTy<TyRef> {
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut set = Vec::new();
        self.fields.values().for_each(|v| {
            set.extend(&v.0.free_type_vars());
        });

        if let Some(dyn_ty) = &self.dyn_ty {
            set.extend(&dyn_ty.0.free_type_vars());
        }

        set
    }

    pub(crate) fn normalize_inner(&self, free: &Substitutions) -> Self {
        let fields = self
            .fields
            .iter()
            .map(|(k, v)| (k.clone(), v.0.normalize_inner(free).into()))
            .collect();

        let dyn_ty = self
            .dyn_ty
            .clone()
            .map(|dyn_ty| dyn_ty.0.normalize_inner(free).into());

        Self {
            fields,
            dyn_ty,
            open: self.open,
        }
    }
}
