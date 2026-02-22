use std::fmt;
use std::sync::Arc;

use derive_more::Debug;
use rustc_hash::FxHashMap;

use smol_str::SmolStr;

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

    /// A type alias name wrapping the fully expanded inner type.
    /// Display shows just the alias name; the inner type is preserved for
    /// structural transparency (e.g. field access on a Named attrset).
    #[debug("Named({_0:?}, {_1:?})")]
    Named(SmolStr, TyRef),

    /// Negation type — `~T`. Used in Boolean-Algebraic Subtyping (BAS) for
    /// precise else-branch narrowing. For example, when `isNull x` is false,
    /// x gets type `a & ~null`. Only produced on atoms (primitives); compound
    /// negation is not needed.
    #[debug("Neg({_0:?})")]
    Neg(TyRef),

    /// The uninhabited (bottom) type, representing contradictions like
    /// `int & ~int`. No values inhabit this type. Displayed as `never`.
    #[debug("Bottom")]
    Bottom,

    /// The universal (top) type, representing tautologies like
    /// `int | ~int`. All values inhabit this type. Displayed as `any`.
    /// Dual to Bottom: identity for intersection (`A & any = A`),
    /// absorbing for union (`A | any = any`).
    #[debug("Top")]
    Top,
}

/// Arc-wrapped OutputTy for recursive type structures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[debug("{_0:?}")]
pub struct TyRef(pub Arc<OutputTy>);

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
        // TyVar is the only leaf that transforms (renumbering); handle it
        // explicitly, then delegate structural recursion to map_children.
        if let OutputTy::TyVar(x) = self {
            let new_idx = free.get(x).unwrap();
            return OutputTy::TyVar(*new_idx);
        }
        self.map_children(&mut |child| child.normalize_inner(free))
    }

    /// Returns true if any Lambda in this type has a non-primitive param type.
    /// Such types can't be precisely generated in PBT because the `if param == <value>`
    /// code generation pattern doesn't fully constrain non-primitive params in
    /// SimpleSub's polarity-aware canonicalization.
    pub fn has_non_primitive_lambda_param(&self) -> bool {
        // Lambda has a special check on the param type before recursing.
        if let OutputTy::Lambda { param, .. } = self {
            if !matches!(&*param.0, OutputTy::Primitive(_) | OutputTy::TyVar(_)) {
                return true;
            }
        }
        let mut found = false;
        self.for_each_child(&mut |child| {
            if !found {
                found = child.has_non_primitive_lambda_param();
            }
        });
        found
    }

    /// Returns true if this type or any of its children contains a Union or Intersection.
    pub fn contains_union_or_intersection(&self) -> bool {
        match self {
            OutputTy::Union(_) | OutputTy::Intersection(_) => true,
            _ => {
                let mut found = false;
                self.for_each_child(&mut |child| {
                    if !found {
                        found = child.contains_union_or_intersection();
                    }
                });
                found
            }
        }
    }

    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        self.collect_free_type_vars(&mut result, &mut seen);
        result
    }

    fn collect_free_type_vars(&self, result: &mut Vec<u32>, seen: &mut rustc_hash::FxHashSet<u32>) {
        if let OutputTy::TyVar(x) = self {
            if seen.insert(*x) {
                result.push(*x);
            }
            return;
        }
        self.for_each_child(&mut |child| child.collect_free_type_vars(result, seen));
    }

    // ==========================================================================
    // Child traversal helpers
    // ==========================================================================
    //
    // Centralise the "recurse into direct children" logic so that new OutputTy
    // variants only need one update site. These are intentionally shallow — they
    // apply `f` to each direct child but do NOT recurse; callers compose
    // recursion themselves.

    /// Apply `f` to every direct child, producing a new OutputTy with the same
    /// variant structure. Leaf variants (TyVar, Primitive) are returned as-is.
    pub fn map_children(&self, f: &mut impl FnMut(&OutputTy) -> OutputTy) -> OutputTy {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {
                self.clone()
            }
            OutputTy::List(inner) => OutputTy::List(f(&inner.0).into()),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: f(&param.0).into(),
                body: f(&body.0).into(),
            },
            OutputTy::AttrSet(attr) => {
                let fields = attr
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), f(&v.0).into()))
                    .collect();
                let dyn_ty = attr.dyn_ty.as_ref().map(|d| f(&d.0).into());
                OutputTy::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            OutputTy::Union(members) => {
                OutputTy::Union(members.iter().map(|m| f(&m.0).into()).collect())
            }
            OutputTy::Intersection(members) => {
                OutputTy::Intersection(members.iter().map(|m| f(&m.0).into()).collect())
            }
            OutputTy::Named(name, inner) => OutputTy::Named(name.clone(), f(&inner.0).into()),
            OutputTy::Neg(inner) => OutputTy::Neg(f(&inner.0).into()),
        }
    }

    /// Visit every direct child for read-only inspection. Leaf variants
    /// (TyVar, Primitive) have no children, so `f` is never called on them.
    pub fn for_each_child(&self, f: &mut impl FnMut(&OutputTy)) {
        match self {
            OutputTy::TyVar(_) | OutputTy::Primitive(_) | OutputTy::Bottom | OutputTy::Top => {}
            OutputTy::List(inner) => f(&inner.0),
            OutputTy::Lambda { param, body } => {
                f(&param.0);
                f(&body.0);
            }
            OutputTy::AttrSet(attr) => {
                for v in attr.fields.values() {
                    f(&v.0);
                }
                if let Some(dyn_ty) = &attr.dyn_ty {
                    f(&dyn_ty.0);
                }
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for m in members {
                    f(&m.0);
                }
            }
            OutputTy::Named(_, inner) => f(&inner.0),
            OutputTy::Neg(inner) => f(&inner.0),
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
            OutputTy::Named(name, _) => write!(f, "{name}"),
            OutputTy::Neg(inner) => {
                // Parenthesize compound types inside negation for clarity.
                let needs_parens = matches!(
                    &*inner.0,
                    OutputTy::Union(_) | OutputTy::Intersection(_) | OutputTy::Lambda { .. }
                );
                if needs_parens {
                    write!(f, "~({inner})")
                } else {
                    write!(f, "~{inner}")
                }
            }
            OutputTy::Bottom => write!(f, "never"),
            OutputTy::Top => write!(f, "any"),
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
            // Number displays as "int | float" to match user expectations. This is
            // distinct from OutputTy::Union([Int, Float]) which would be structurally
            // different but semantically equivalent in display.
            PrimitiveTy::Number => write!(f, "int | float"),
        }
    }
}

impl fmt::Display for AttrSetTy<TyRef> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        let mut first = true;
        for (k, v) in self.fields.iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            let opt = if self.optional_fields.contains(k) {
                "?"
            } else {
                ""
            };
            write!(f, "{k}{opt}: {v}")?;
        }
        if let Some(dyn_ty) = &self.dyn_ty {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "_: {dyn_ty}")?;
        }
        if self.open {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        write!(f, " }}")
    }
}

impl AttrSetTy<TyRef> {
    /// Collect free type variables in order of first appearance, deduplicated.
    pub fn free_type_vars(&self) -> Vec<u32> {
        let mut result = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        for v in self.fields.values() {
            for var in v.0.free_type_vars() {
                if seen.insert(var) {
                    result.push(var);
                }
            }
        }
        if let Some(dyn_ty) = &self.dyn_ty {
            for var in dyn_ty.0.free_type_vars() {
                if seen.insert(var) {
                    result.push(var);
                }
            }
        }
        result
    }
}
