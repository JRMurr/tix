// ==============================================================================
// Hegel generators for Nix source text paired with its expected type
// ==============================================================================
//
// Generation is imperative: every helper takes `&TestCase` and draws as it
// goes, so recursion is a plain depth parameter and dependent choices are
// ordinary control flow.

use std::collections::BTreeMap;

use hegel::generators;
use hegel::TestCase;
use lang_ast::{BoolBinOp, OverloadBinOp};
use lang_ty::hegel_gen::{idents, prims, shuffle, LITERAL_PRIMS};
use lang_ty::raw_ty::{raw_spread_free_vars, RawTy};
use lang_ty::PrimitiveTy;
use smol_str::SmolStr;

use super::NixTextStr;

/// Nesting depth of operator chains inside a primitive literal.
const OP_DEPTH: u32 = 3;
/// Default probability of stopping recursion early (before `depth` hits zero).
const STOP_EARLY: f64 = 0.5;
/// Early-stop probability for the deep combined generator, so depth-8 trees
/// actually occur.
const STOP_EARLY_DEEP: f64 = 0.25;
const COMBINED_DEPTH: u32 = 8;
const FROM_TY_DEPTH: u32 = 4;
const MAX_UNION_MEMBERS: usize = 4;
const MAX_ATTR_FIELDS: usize = 4;
const MAX_MERGED_ATTRS: usize = 2;
const MAX_WRAP_EXTRA_FIELDS: usize = 4;

const BOOL_OPS: [BoolBinOp; 3] = [BoolBinOp::And, BoolBinOp::Or, BoolBinOp::Implication];
const OVERLOAD_OPS: [OverloadBinOp; 4] = [
    OverloadBinOp::Add,
    OverloadBinOp::Sub,
    OverloadBinOp::Mul,
    OverloadBinOp::Div,
];

fn stop(tc: &TestCase, depth: u32) -> bool {
    stop_with(tc, depth, STOP_EARLY)
}

fn stop_with(tc: &TestCase, depth: u32, stop_prob: f64) -> bool {
    depth == 0 || tc.draw(generators::weighted_booleans(stop_prob))
}

fn overload_op(tc: &TestCase) -> String {
    tc.draw(generators::sampled_from(OVERLOAD_OPS.to_vec()))
        .to_string()
}

// ------------------------------------------------------------------------------
// Primitive literals (with operator chains that preserve the type)
// ------------------------------------------------------------------------------

fn bool_src(tc: &TestCase, depth: u32) -> NixTextStr {
    if stop(tc, depth) {
        return tc.draw(generators::booleans()).to_string();
    }
    let l = bool_src(tc, depth - 1);
    let r = bool_src(tc, depth - 1);
    let op: String = tc.draw(generators::sampled_from(BOOL_OPS.to_vec())).into();
    format!("({l}) {op} ({r})")
}

fn int_src(tc: &TestCase, depth: u32) -> NixTextStr {
    if stop(tc, depth) {
        return tc.draw(generators::integers::<i32>()).to_string();
    }
    let l = int_src(tc, depth - 1);
    let r = int_src(tc, depth - 1);
    let op = overload_op(tc);
    format!("({l}) {op} ({r})")
}

fn float_src(tc: &TestCase, depth: u32) -> NixTextStr {
    if stop(tc, depth) {
        let f = tc.draw(generators::floats::<f64>().min_value(-1.0).max_value(2.0));
        return format!("{f:.4}");
    }
    // At least one operand is a float; it may sit on either side.
    let float = float_src(tc, depth - 1);
    let other = if tc.draw(generators::booleans()) {
        float_src(tc, depth - 1)
    } else {
        int_src(tc, depth - 1)
    };
    let (l, r) = if tc.draw(generators::booleans()) {
        (float, other)
    } else {
        (other, float)
    };
    let op = overload_op(tc);
    format!("({l}) {op} ({r})")
}

fn str_src(tc: &TestCase) -> NixTextStr {
    let s = tc.draw(idents());
    format!("''{s}''")
}

pub(super) fn prim_src(tc: &TestCase, prim: PrimitiveTy) -> NixTextStr {
    match prim {
        PrimitiveTy::Null => "null".to_string(),
        PrimitiveTy::Bool => bool_src(tc, OP_DEPTH),
        PrimitiveTy::Int => int_src(tc, OP_DEPTH),
        PrimitiveTy::Float => float_src(tc, OP_DEPTH),
        PrimitiveTy::String => str_src(tc),
        PrimitiveTy::Path | PrimitiveTy::Uri | PrimitiveTy::Number => {
            unreachable!("not produced by hegel_gen::prims")
        }
    }
}

fn prim_leaf(tc: &TestCase) -> (RawTy, NixTextStr) {
    let prim = tc.draw(prims());
    (RawTy::Primitive(prim), prim_src(tc, prim))
}

// ------------------------------------------------------------------------------
// Type-preserving wrappers
// ------------------------------------------------------------------------------

/// Wrap `text` in a let-binding or an attrset field selection (or leave it).
pub(super) fn wrap(tc: &TestCase, text: NixTextStr) -> NixTextStr {
    match tc.draw(generators::integers::<u8>().max_value(2)) {
        0 => text,
        1 => {
            let ident = tc.draw(idents());
            format!("(let {ident} = ({text}); in {ident})")
        }
        _ => {
            let mut names: Vec<SmolStr> = tc.draw(
                generators::vecs(idents())
                    .min_size(1)
                    .max_size(MAX_WRAP_EXTRA_FIELDS + 1)
                    .unique(true),
            );
            let target = names.pop().expect("min_size(1)");
            let mut fields: Vec<String> = names
                .into_iter()
                .map(|name| {
                    let prim = tc.draw(prims());
                    format!("{name}=({});", prim_src(tc, prim))
                })
                .collect();
            fields.push(format!("{target}=({text});"));
            format!("(({{{}}}).{target})", fields.join(" "))
        }
    }
}

// ------------------------------------------------------------------------------
// Compound constructors
// ------------------------------------------------------------------------------

fn prim_assert_builtin(prim: PrimitiveTy) -> &'static str {
    match prim {
        PrimitiveTy::Int => "__pbt_assert_int",
        PrimitiveTy::Float => "__pbt_assert_float",
        PrimitiveTy::Bool => "__pbt_assert_bool",
        PrimitiveTy::String => "__pbt_assert_string",
        PrimitiveTy::Null => "__pbt_assert_null",
        PrimitiveTy::Path | PrimitiveTy::Uri | PrimitiveTy::Number => {
            unreachable!("not produced by hegel_gen::prims")
        }
    }
}

/// A lambda whose param is either assertion-constrained to a primitive
/// ("fully known") or unused and therefore a fresh type variable ("generic").
pub(super) fn func(
    tc: &TestCase,
    (body_ty, body_text): (RawTy, NixTextStr),
) -> (RawTy, NixTextStr) {
    if tc.draw(generators::booleans()) {
        let prim = tc.draw(prims());
        let mut num_free_vars = 0;
        let param = RawTy::Primitive(prim).offset_free_vars(&mut num_free_vars);
        let body = body_ty.offset_free_vars(&mut num_free_vars);
        let builtin = prim_assert_builtin(prim);
        let text = format!("(__pbt_p: let __pbt_chk = {builtin} __pbt_p; in ({body_text}))");
        return (lambda(param, body), text);
    }

    let param = RawTy::TyVar((body_ty.free_type_vars().len() + 1) as u32);
    (lambda(param, body_ty), format!("(__pbt_p: {body_text})"))
}

fn lambda(param: RawTy, body: RawTy) -> RawTy {
    RawTy::Lambda {
        param: Box::new(param),
        body: Box::new(body),
    }
}

/// One to `MAX_MERGED_ATTRS` attrset literals joined with `//`; each field's
/// value is drawn from `inner`.
pub(super) fn attrs(
    tc: &TestCase,
    inner: impl Fn(&TestCase) -> (RawTy, NixTextStr),
) -> (RawTy, NixTextStr) {
    let n = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(MAX_MERGED_ATTRS),
    );
    let mut merged: BTreeMap<SmolStr, RawTy> = BTreeMap::new();
    let mut texts = Vec::with_capacity(n);
    for _ in 0..n {
        let names: Vec<SmolStr> = tc.draw(
            generators::vecs(idents())
                .min_size(1)
                .max_size(MAX_ATTR_FIELDS)
                .unique(true),
        );
        let mut fields = Vec::with_capacity(names.len());
        for name in names {
            let (ty, text) = inner(tc);
            fields.push(format!("{name}=({text});"));
            merged.insert(name, ty);
        }
        texts.push(format!("({{{}}})", fields.join(" ")));
    }
    let spread = raw_spread_free_vars(&merged, &mut 0);
    (RawTy::AttrSet(spread), texts.join(" // "))
}

fn list(tc: &TestCase, inner: impl Fn(&TestCase) -> (RawTy, NixTextStr)) -> (RawTy, NixTextStr) {
    let (ty, text) = inner(tc);
    (RawTy::List(Box::new(ty)), format!("[({text})]"))
}

/// Recursive generator over every construct the checker infers precisely:
/// primitives, wrappers, lists, lambdas, attrsets, and if-then-else unions.
pub(super) fn nix_text(tc: &TestCase, depth: u32) -> (RawTy, NixTextStr) {
    nix_text_with(tc, depth, STOP_EARLY)
}

fn nix_text_with(tc: &TestCase, depth: u32, stop_prob: f64) -> (RawTy, NixTextStr) {
    if stop_with(tc, depth, stop_prob) {
        return prim_leaf(tc);
    }
    let inner = |tc: &TestCase| nix_text_with(tc, depth - 1, stop_prob);
    // Weights: 3 wrapped / 3 list / 3 func / 3 attr / 2 union.
    match tc.draw(generators::integers::<u8>().max_value(13)) {
        0..=2 => {
            let (ty, text) = inner(tc);
            (ty, wrap(tc, text))
        }
        3..=5 => list(tc, inner),
        6..=8 => func(tc, inner(tc)),
        9..=11 => attrs(tc, inner),
        _ => {
            let (a_ty, a_text) = inner(tc);
            let (b_ty, b_text) = inner(tc);
            (
                RawTy::Union(vec![a_ty, b_ty]),
                format!("(if true then ({a_text}) else ({b_text}))"),
            )
        }
    }
}

// ------------------------------------------------------------------------------
// Focused generators for the split typing tests
// ------------------------------------------------------------------------------

/// Primitives with operator chains, optionally wrapped.
#[hegel::composite]
pub(super) fn primitive(tc: &TestCase) -> (RawTy, NixTextStr) {
    let (ty, text) = prim_leaf(tc);
    (ty, wrap(tc, text))
}

/// Lists and attrsets of primitives, including `//` merging.
#[hegel::composite]
pub(super) fn structural(tc: &TestCase) -> (RawTy, NixTextStr) {
    let (ty, text) = if tc.draw(generators::booleans()) {
        list(tc, prim_leaf)
    } else {
        attrs(tc, prim_leaf)
    };
    (ty, wrap(tc, text))
}

/// Lambdas (assertion-constrained + generic) with primitive or one-level
/// structural bodies. Exercises generalization, extrusion, and early
/// canonicalization.
#[hegel::composite]
pub(super) fn lambda_expr(tc: &TestCase) -> (RawTy, NixTextStr) {
    let body = match tc.draw(generators::integers::<u8>().max_value(2)) {
        0 => prim_leaf(tc),
        1 => list(tc, prim_leaf),
        _ => attrs(tc, prim_leaf),
    };
    let (ty, text) = func(tc, body);
    (ty, wrap(tc, text))
}

/// Full recursive generation to `depth`.
#[hegel::composite]
pub(super) fn nix_texts(tc: &TestCase, depth: u32) -> (RawTy, NixTextStr) {
    nix_text(tc, depth)
}

// ------------------------------------------------------------------------------
// Type-directed generation
// ------------------------------------------------------------------------------

/// A `RawTy` that `text_from_raw_ty` can express precisely as Nix code:
/// primitives, lists, attrsets, unions, and lambdas whose param is a
/// primitive or a fresh type variable (unique per lambda, never shared).
/// `next_var` numbers the lambda params.
fn expressible_raw_ty(tc: &TestCase, depth: u32, next_var: &mut u32) -> RawTy {
    if stop(tc, depth) {
        return RawTy::Primitive(tc.draw(prims()));
    }
    // Weights: 3 list / 3 lambda / 3 attrset / 2 union.
    match tc.draw(generators::integers::<u8>().max_value(10)) {
        0..=2 => RawTy::List(Box::new(expressible_raw_ty(tc, depth - 1, next_var))),
        3..=5 => {
            let param = if tc.draw(generators::booleans()) {
                RawTy::Primitive(tc.draw(prims()))
            } else {
                *next_var += 1;
                RawTy::TyVar(*next_var)
            };
            let body = expressible_raw_ty(tc, depth - 1, next_var);
            lambda(param, body)
        }
        6..=8 => {
            let names: Vec<SmolStr> = tc.draw(
                generators::vecs(idents())
                    .max_size(MAX_ATTR_FIELDS)
                    .unique(true),
            );
            let fields = names
                .into_iter()
                .map(|n| (n, expressible_raw_ty(tc, depth - 1, next_var)))
                .collect();
            RawTy::AttrSet(fields)
        }
        _ => {
            let n = tc.draw(
                generators::integers::<usize>()
                    .min_value(2)
                    .max_value(MAX_UNION_MEMBERS),
            );
            RawTy::Union(
                (0..n)
                    .map(|_| expressible_raw_ty(tc, depth - 1, next_var))
                    .collect(),
            )
        }
    }
}

/// Nix source whose inferred type is `ty` (for expressible types only).
pub(super) fn text_from_raw_ty(tc: &TestCase, ty: &RawTy) -> NixTextStr {
    let inner = match ty {
        RawTy::Primitive(prim) => prim_src(tc, *prim),
        RawTy::List(inner) => format!("[({})]", text_from_raw_ty(tc, inner)),
        RawTy::Lambda { param, body } => {
            let body = text_from_raw_ty(tc, body);
            match param.as_ref() {
                RawTy::Primitive(prim) => {
                    let builtin = prim_assert_builtin(*prim);
                    format!("(__pbt_p: let __pbt_chk = {builtin} __pbt_p; in ({body}))")
                }
                RawTy::TyVar(_) => format!("(__pbt_p: {body})"),
                other => unreachable!("inexpressible lambda param {other:?}"),
            }
        }
        RawTy::AttrSet(fields) => {
            let mut fields: Vec<String> = fields
                .iter()
                .map(|(key, val)| format!("\"{key}\"=({});", text_from_raw_ty(tc, val)))
                .collect();
            shuffle(tc, &mut fields);
            format!("({{{}}})", fields.join(" "))
        }
        RawTy::Union(members) => members
            .iter()
            .map(|m| text_from_raw_ty(tc, m))
            .rev()
            .reduce(|else_branch, then_branch| {
                format!("(if true then ({then_branch}) else ({else_branch}))")
            })
            .expect("union has at least 2 members"),
        RawTy::Named(_, inner) => text_from_raw_ty(tc, inner),
        other => unreachable!("inexpressible type {other:?}"),
    };
    wrap(tc, inner)
}

/// Type-directed generation: draw an expressible type, then source for it.
pub(super) fn nix_text_from_ty(tc: &TestCase) -> (RawTy, NixTextStr) {
    let ty = expressible_raw_ty(tc, FROM_TY_DEPTH, &mut 0);
    let text = text_from_raw_ty(tc, &ty);
    (ty, text)
}

// ------------------------------------------------------------------------------
// Unions of distinct primitives
// ------------------------------------------------------------------------------

/// `n` distinct literal primitives, in drawn order.
pub(super) fn distinct_prims(tc: &TestCase, n: usize) -> Vec<PrimitiveTy> {
    let mut prims = LITERAL_PRIMS.to_vec();
    shuffle(tc, &mut prims);
    prims.truncate(n);
    prims
}

/// Two distinct primitives in if-then-else: an exact 2-member union.
pub(super) fn union_prim_if_else(tc: &TestCase) -> (RawTy, NixTextStr) {
    let prims = distinct_prims(tc, 2);
    let (a, b) = (prim_src(tc, prims[0]), prim_src(tc, prims[1]));
    let ty = RawTy::Union(prims.into_iter().map(RawTy::Primitive).collect());
    (ty, format!("(if true then ({a}) else ({b}))"))
}

/// Three distinct primitives in nested if-then-else: an exact 3-member union.
pub(super) fn union_three_way(tc: &TestCase) -> (RawTy, NixTextStr) {
    let prims = distinct_prims(tc, 3);
    let (a, b, c) = (
        prim_src(tc, prims[0]),
        prim_src(tc, prims[1]),
        prim_src(tc, prims[2]),
    );
    let ty = RawTy::Union(prims.into_iter().map(RawTy::Primitive).collect());
    (
        ty,
        format!("(if true then ({a}) else (if true then ({b}) else ({c})))"),
    )
}

/// Everything at once: deep recursive generation, type-directed generation,
/// and the focused union generators. Weights 7/1/1/1.
#[hegel::composite]
pub(super) fn combined(tc: &TestCase) -> (RawTy, NixTextStr) {
    match tc.draw(generators::integers::<u8>().max_value(9)) {
        0..=6 => nix_text_with(tc, COMBINED_DEPTH, STOP_EARLY_DEEP),
        7 => nix_text_from_ty(tc),
        8 => union_prim_if_else(tc),
        _ => union_three_way(tc),
    }
}
