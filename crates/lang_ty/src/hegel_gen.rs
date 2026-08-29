//! Hegel generators shared across crates (see `raw_ty` for the `RawTy` tree).
//!
//! Enabled under `cfg(test)` or the `hegel_support` feature so downstream
//! crates' tests can reuse them.

use std::collections::BTreeMap;

use hegel::generators::{self, Generator};
use hegel::TestCase;
use smol_str::SmolStr;

use crate::raw_ty::RawTy;
use crate::PrimitiveTy;

/// Primitives that have a Nix literal form. `Path`/`Uri` are excluded because
/// the Nix-text generators have no literal for them; `Number` is synthetic.
pub const LITERAL_PRIMS: [PrimitiveTy; 5] = [
    PrimitiveTy::Null,
    PrimitiveTy::Bool,
    PrimitiveTy::Int,
    PrimitiveTy::Float,
    PrimitiveTy::String,
];

/// Every `PrimitiveTy` variant, including synthetic `Number`.
pub const ALL_PRIMS: [PrimitiveTy; 8] = [
    PrimitiveTy::Null,
    PrimitiveTy::Bool,
    PrimitiveTy::Int,
    PrimitiveTy::Float,
    PrimitiveTy::String,
    PrimitiveTy::Path,
    PrimitiveTy::Uri,
    PrimitiveTy::Number,
];

#[hegel::composite]
pub fn prims(tc: &TestCase) -> PrimitiveTy {
    tc.draw(generators::sampled_from(LITERAL_PRIMS.to_vec()))
}

#[hegel::composite]
pub fn all_prims(tc: &TestCase) -> PrimitiveTy {
    tc.draw(generators::sampled_from(ALL_PRIMS.to_vec()))
}

#[hegel::composite]
pub fn idents(tc: &TestCase) -> SmolStr {
    tc.draw(generators::from_regex(r"_pbt_[a-zA-Z0-9_]{1,10}").map(SmolStr::from))
}

/// Recursive `RawTy` generator. `depth` bounds nesting; branch weights match
/// `arbitrary::arb_raw_ty`. Draws lean toward leaves so trees stay small.
#[hegel::composite]
pub fn raw_tys(tc: &TestCase, depth: u32) -> RawTy {
    // Leaf weights: 8 prim / 1 tyvar / 1 top / 1 bottom.
    const LEAF_WEIGHT: u32 = 11;
    // Node weights: 3 list / 3 lambda / 3 attrset / 2 union / 2 inter / 1 neg / 1 named.
    const NODE_WEIGHT: u32 = 15;
    const MAX_SET_MEMBERS: usize = 4;
    const MAX_FIELDS: usize = 4;

    let total = if depth == 0 {
        LEAF_WEIGHT
    } else {
        LEAF_WEIGHT + NODE_WEIGHT
    };
    let pick = tc.draw(generators::integers::<u32>().max_value(total - 1));

    match pick {
        0..=7 => RawTy::Primitive(tc.draw(prims())),
        8 => RawTy::TyVar(tc.draw(generators::integers::<u32>().min_value(1).max_value(8))),
        9 => RawTy::Top,
        10 => RawTy::Bottom,
        11..=13 => RawTy::List(Box::new(tc.draw(raw_tys(depth - 1)))),
        14..=16 => RawTy::Lambda {
            param: Box::new(tc.draw(raw_tys(depth - 1))),
            body: Box::new(tc.draw(raw_tys(depth - 1))),
        },
        17..=19 => {
            let names: Vec<SmolStr> =
                tc.draw(generators::vecs(idents()).max_size(MAX_FIELDS).unique(true));
            let mut fields = BTreeMap::new();
            for name in names {
                fields.insert(name, tc.draw(raw_tys(depth - 1)));
            }
            RawTy::AttrSet(fields)
        }
        20..=21 => RawTy::Union(
            tc.draw(
                generators::vecs(raw_tys(depth - 1))
                    .min_size(2)
                    .max_size(MAX_SET_MEMBERS),
            ),
        ),
        22..=23 => RawTy::Intersection(
            tc.draw(
                generators::vecs(raw_tys(depth - 1))
                    .min_size(2)
                    .max_size(MAX_SET_MEMBERS),
            ),
        ),
        24 => RawTy::Neg(Box::new(tc.draw(raw_tys(depth - 1)))),
        25 => RawTy::Named(tc.draw(idents()), Box::new(tc.draw(raw_tys(depth - 1)))),
        _ => unreachable!("pick < total"),
    }
}

/// In-place Fisher-Yates shuffle driven by drawn indices, so the permutation
/// shrinks like any other value.
pub fn shuffle<T>(tc: &TestCase, items: &mut [T]) {
    for i in (1..items.len()).rev() {
        let j = tc.draw(generators::integers::<usize>().max_value(i));
        items.swap(i, j);
    }
}

/// Recursively shuffle every Union/Intersection member list.
pub fn shuffle_set_ops(tc: &TestCase, ty: &mut RawTy) {
    match ty {
        RawTy::Union(members) | RawTy::Intersection(members) => {
            shuffle(tc, members);
            for m in members {
                shuffle_set_ops(tc, m);
            }
        }
        RawTy::List(inner) | RawTy::Neg(inner) | RawTy::Named(_, inner) => {
            shuffle_set_ops(tc, inner)
        }
        RawTy::Lambda { param, body } => {
            shuffle_set_ops(tc, param);
            shuffle_set_ops(tc, body);
        }
        RawTy::AttrSet(fields) => {
            for v in fields.values_mut() {
                shuffle_set_ops(tc, v);
            }
        }
        RawTy::TyVar(_) | RawTy::Primitive(_) | RawTy::Top | RawTy::Bottom => {}
    }
}
