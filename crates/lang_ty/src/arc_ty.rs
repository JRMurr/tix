use std::ops::ControlFlow;

use derive_more::Debug;
use rustc_hash::FxHashMap;

use crate::{AttrSetTy, PrimitiveTy};

// Re-export TyRef from arena module.
pub use crate::arena::TyRef;

// ==============================================================================
// OutputTy — the canonical output representation of types
// ==============================================================================
//
// During inference we use `Ty<TyId>` which has 5 variants (no unions/intersections).
// After inference, canonicalization produces `OutputTy` which adds Union and Intersection.
// This separation makes it impossible to accidentally construct a union during inference.
//
// TyRef is now `la_arena::Idx<OutputTy>` — a 4-byte Copy index into a TypeArena.
// All TyRef children are meaningless without their owning arena.

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

    /// A union of types (e.g. `int | string`).
    #[debug("Union({_0:?})")]
    Union(Vec<TyRef>),

    /// An intersection of types (e.g. `(int -> int) & (string -> string)`).
    #[debug("Intersection({_0:?})")]
    Intersection(Vec<TyRef>),

    /// A type alias name wrapping the fully expanded inner type.
    #[debug("Named({_0:?}, {_1:?})")]
    Named(smol_str::SmolStr, TyRef),

    /// Negation type — `~T`.
    #[debug("Neg({_0:?})")]
    Neg(TyRef),

    /// The uninhabited (bottom) type. Displayed as `never`.
    #[debug("Bottom")]
    Bottom,

    /// The universal (top) type. Displayed as `any`.
    #[debug("Top")]
    Top,

    /// A type that lives in an external arena (zero-copy import from another file).
    /// Treated as a leaf: no TyRef children in the owning arena.
    #[debug("Extern({_0:?})")]
    Extern(crate::arena::OwnedTy),
}

impl PartialOrd for OutputTy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OutputTy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        /// Discriminant index for ordering OutputTy variants.
        fn disc(ty: &OutputTy) -> u8 {
            match ty {
                OutputTy::Bottom => 0,
                OutputTy::Top => 1,
                OutputTy::Primitive(_) => 2,
                OutputTy::TyVar(_) => 3,
                OutputTy::List(_) => 4,
                OutputTy::Lambda { .. } => 5,
                OutputTy::AttrSet(_) => 6,
                OutputTy::Union(_) => 7,
                OutputTy::Intersection(_) => 8,
                OutputTy::Named(..) => 9,
                OutputTy::Neg(_) => 10,
                OutputTy::Extern(_) => 11,
            }
        }

        let d = disc(self).cmp(&disc(other));
        if d != Ordering::Equal {
            return d;
        }

        match (self, other) {
            (OutputTy::Bottom, OutputTy::Bottom) | (OutputTy::Top, OutputTy::Top) => {
                Ordering::Equal
            }
            (OutputTy::Primitive(a), OutputTy::Primitive(b)) => a.cmp(b),
            (OutputTy::TyVar(a), OutputTy::TyVar(b)) => a.cmp(b),
            (OutputTy::List(a), OutputTy::List(b)) => a.cmp(b),
            (
                OutputTy::Lambda {
                    param: pa,
                    body: ba,
                },
                OutputTy::Lambda {
                    param: pb,
                    body: bb,
                },
            ) => pa.cmp(pb).then_with(|| ba.cmp(bb)),
            (OutputTy::AttrSet(a), OutputTy::AttrSet(b)) => a.cmp(b),
            (OutputTy::Union(a), OutputTy::Union(b))
            | (OutputTy::Intersection(a), OutputTy::Intersection(b)) => a.cmp(b),
            (OutputTy::Named(na, ta), OutputTy::Named(nb, tb)) => {
                na.cmp(nb).then_with(|| ta.cmp(tb))
            }
            (OutputTy::Neg(a), OutputTy::Neg(b)) => a.cmp(b),
            (OutputTy::Extern(a), OutputTy::Extern(b)) => a.cmp(b),
            _ => unreachable!(),
        }
    }
}

pub type Substitutions = FxHashMap<u32, u32>;

// ==============================================================================
// Display helpers — used by arena.rs display code
// ==============================================================================

/// Sentinel index for type variables that should display as `?` (unknown type).
pub(crate) const UNKNOWN_TYVAR: u32 = u32::MAX;

/// Convert a type variable index to a letter-based name: 0→a, 1→b, ..., 25→z, 26→a1, ...
pub(crate) fn tyvar_name(idx: u32) -> String {
    if idx == UNKNOWN_TYVAR {
        return "?".to_string();
    }
    let letter = (b'a' + (idx % 26) as u8) as char;
    let suffix = idx / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{letter}{suffix}")
    }
}

/// Lambda params need parens if they are themselves lambdas, unions, or intersections.
pub(crate) fn needs_parens_in_lambda_param(ty: &OutputTy) -> bool {
    matches!(
        ty,
        OutputTy::Lambda { .. } | OutputTy::Union(_) | OutputTy::Intersection(_)
    )
}

/// Union members need parens if they are lambdas.
pub(crate) fn needs_parens_in_union_member(ty: &OutputTy) -> bool {
    matches!(ty, OutputTy::Lambda { .. })
}

/// Intersection members need parens if they are lambdas or unions.
pub(crate) fn needs_parens_in_intersection_member(ty: &OutputTy) -> bool {
    matches!(ty, OutputTy::Lambda { .. } | OutputTy::Union(_))
}

/// Negation operands need parens if they are unions, intersections, or lambdas.
pub(crate) fn needs_parens_in_neg(ty: &OutputTy) -> bool {
    matches!(
        ty,
        OutputTy::Union(_) | OutputTy::Intersection(_) | OutputTy::Lambda { .. }
    )
}

// ==============================================================================
// DisplayConfig — controls truncation for large types
// ==============================================================================

#[derive(Debug, Clone, Copy)]
pub struct DisplayConfig {
    pub max_fields: usize,
    pub max_members: usize,
    pub max_depth: usize,
    pub max_chars: usize,
}

impl DisplayConfig {
    pub fn full() -> Self {
        Self {
            max_fields: 0,
            max_members: 0,
            max_depth: 0,
            max_chars: 0,
        }
    }

    pub fn cli() -> Self {
        Self {
            max_fields: 10,
            max_members: 8,
            max_depth: 5,
            max_chars: 2000,
        }
    }

    pub fn hover() -> Self {
        Self {
            max_fields: 15,
            max_members: 8,
            max_depth: 6,
            max_chars: 4000,
        }
    }

    pub fn inlay() -> Self {
        Self {
            max_fields: 3,
            max_members: 3,
            max_depth: 2,
            max_chars: 80,
        }
    }

    pub fn completion() -> Self {
        Self {
            max_fields: 3,
            max_members: 3,
            max_depth: 2,
            max_chars: 120,
        }
    }

    pub fn diagnostic() -> Self {
        Self {
            max_fields: 8,
            max_members: 5,
            max_depth: 4,
            max_chars: 500,
        }
    }

    pub(crate) fn is_unlimited(&self) -> bool {
        self.max_fields == 0 && self.max_members == 0 && self.max_depth == 0 && self.max_chars == 0
    }
}

// ==============================================================================
// Child traversal helpers on OutputTy
// ==============================================================================
//
// These iterate over the direct TyRef children stored in the enum variants.
// They do NOT need the arena — children are TyRef (Idx) values embedded in
// the variant. Only RESOLVING a TyRef to its OutputTy requires the arena.

impl OutputTy {
    /// Apply `f` to every direct child TyRef, producing a new OutputTy with the
    /// same variant structure.
    pub(crate) fn map_children(&self, f: &mut impl FnMut(TyRef) -> TyRef) -> OutputTy {
        match self {
            OutputTy::TyVar(_)
            | OutputTy::Primitive(_)
            | OutputTy::Bottom
            | OutputTy::Top
            | OutputTy::Extern(_) => self.clone(),
            OutputTy::List(inner) => OutputTy::List(f(*inner)),
            OutputTy::Lambda { param, body } => OutputTy::Lambda {
                param: f(*param),
                body: f(*body),
            },
            OutputTy::AttrSet(attr) => {
                let fields = attr
                    .fields
                    .iter()
                    .map(|(k, &v)| (k.clone(), f(v)))
                    .collect();
                let dyn_ty = attr.dyn_ty.map(f);
                OutputTy::AttrSet(AttrSetTy {
                    fields,
                    dyn_ty,
                    open: attr.open,
                    optional_fields: attr.optional_fields.clone(),
                })
            }
            OutputTy::Union(members) => {
                OutputTy::Union(members.iter().copied().map(&mut *f).collect())
            }
            OutputTy::Intersection(members) => {
                OutputTy::Intersection(members.iter().copied().map(&mut *f).collect())
            }
            OutputTy::Named(name, inner) => OutputTy::Named(name.clone(), f(*inner)),
            OutputTy::Neg(inner) => OutputTy::Neg(f(*inner)),
        }
    }

    /// Visit every direct child TyRef for read-only inspection.
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(TyRef)) {
        match self {
            OutputTy::TyVar(_)
            | OutputTy::Primitive(_)
            | OutputTy::Bottom
            | OutputTy::Top
            | OutputTy::Extern(_) => {}
            OutputTy::List(inner) => f(*inner),
            OutputTy::Lambda { param, body } => {
                f(*param);
                f(*body);
            }
            OutputTy::AttrSet(attr) => {
                for &v in attr.fields.values() {
                    f(v);
                }
                if let Some(dyn_ty) = attr.dyn_ty {
                    f(dyn_ty);
                }
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for &m in members {
                    f(m);
                }
            }
            OutputTy::Named(_, inner) => f(*inner),
            OutputTy::Neg(inner) => f(*inner),
        }
    }

    /// Like `for_each_child` but supports early exit via `ControlFlow`.
    pub(crate) fn try_for_each_child(
        &self,
        f: &mut impl FnMut(TyRef) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        match self {
            OutputTy::TyVar(_)
            | OutputTy::Primitive(_)
            | OutputTy::Bottom
            | OutputTy::Top
            | OutputTy::Extern(_) => ControlFlow::Continue(()),
            OutputTy::List(inner) => f(*inner),
            OutputTy::Lambda { param, body } => {
                f(*param)?;
                f(*body)
            }
            OutputTy::AttrSet(attr) => {
                for &v in attr.fields.values() {
                    f(v)?;
                }
                if let Some(dyn_ty) = attr.dyn_ty {
                    f(dyn_ty)?;
                }
                ControlFlow::Continue(())
            }
            OutputTy::Union(members) | OutputTy::Intersection(members) => {
                for &m in members {
                    f(m)?;
                }
                ControlFlow::Continue(())
            }
            OutputTy::Named(_, inner) => f(*inner),
            OutputTy::Neg(inner) => f(*inner),
        }
    }
}

impl std::fmt::Display for PrimitiveTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveTy::Null => write!(f, "null"),
            PrimitiveTy::Bool => write!(f, "bool"),
            PrimitiveTy::Int => write!(f, "int"),
            PrimitiveTy::Float => write!(f, "float"),
            PrimitiveTy::String => write!(f, "string"),
            PrimitiveTy::Path => write!(f, "path"),
            PrimitiveTy::Uri => write!(f, "uri"),
            PrimitiveTy::Number => write!(f, "number"),
        }
    }
}
