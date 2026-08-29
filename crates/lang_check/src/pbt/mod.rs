// ==============================================================================
// Property-Based Tests for Type Inference
// ==============================================================================
//
// Generates random Nix source paired with its expected type, then verifies
// that the type checker infers the expected type. Generators live in `gen.rs`.
//
// Coverage:
// - Primitives, lists, lambdas, attrsets — full correctness via `gen::nix_text`
//   and type-directed `gen::nix_text_from_ty`.
// - Union types — via if-then-else in both generators, plus focused tests for
//   2- and 3-member primitive unions. Comparison uses normalize_set_ops.
// - Intersection types — crash-freedom only (can't generate positive-position
//   intersections). Tested via || narrowing, has-field conjunction, and
//   contradictory narrowing patterns.
//
// Known limitations:
// - Unions with duplicate members normalize to one type on the expected side,
//   but inference keeps distinct branch variables; union cases in the broad
//   generators therefore only check crash freedom.
// - Path and Uri have no literal form in the generators.

mod cyclic;
mod frozen;
mod gen;
mod let_bridged_export;
mod partial;
mod stub_compose;
mod type_ops;

use hegel::generators;
use hegel::TestCase;
use lang_ast::Expr;
use lang_ty::hegel_gen::idents;
use lang_ty::raw_ty::RawTy;
use lang_ty::{OutputTy, PrimitiveTy};
use smol_str::SmolStr;

use crate::aliases::TypeAliasRegistry;
use crate::tests::{check_str, check_str_with_aliases, get_inferred_root, raw_to_root};

pub(super) type NixTextStr = String;

const NARROW_VAR: &str = "__narr_x";

fn index(tc: &TestCase, len: usize) -> usize {
    tc.draw(generators::integers::<usize>().max_value(len - 1))
}

/// Two distinct indices into a table of `len` entries.
fn distinct_pair(tc: &TestCase, len: usize) -> (usize, usize) {
    let i = index(tc, len);
    let off = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(len - 1),
    );
    (i, (i + off) % len)
}

fn unique_idents(tc: &TestCase, min: usize, max: usize) -> Vec<SmolStr> {
    tc.draw(
        generators::vecs(idents())
            .min_size(min)
            .max_size(max)
            .unique(true),
    )
}

// ==============================================================================
// Typing tests: inferred root type must equal the generator's expected type
// ==============================================================================

#[track_caller]
fn assert_infers((ty, text): (RawTy, NixTextStr)) {
    let root_ty = get_inferred_root(&text).normalize_vars();
    let expected = raw_to_root(&ty.normalize_vars());
    assert_eq!(root_ty, expected, "source: {text}");
}

/// Like `assert_infers`, but union/intersection cases only check crash
/// freedom (see module doc).
#[track_caller]
fn assert_infers_modulo_unions((ty, text): (RawTy, NixTextStr)) {
    let actual = get_inferred_root(&text)
        .normalize_vars()
        .normalize_set_ops();
    let expected = raw_to_root(&ty.normalize_vars()).normalize_set_ops();
    if expected.contains_union_or_intersection() || actual.contains_union_or_intersection() {
        return;
    }
    assert_eq!(actual, expected, "source: {text}");
}

#[hegel::test(test_cases = 256)]
fn test_primitive_typing(tc: TestCase) {
    assert_infers(tc.draw(gen::primitive()));
}

#[hegel::test(test_cases = 256)]
fn test_structural_typing(tc: TestCase) {
    assert_infers(tc.draw(gen::structural()));
}

#[hegel::test(test_cases = 256)]
fn test_lambda_typing(tc: TestCase) {
    assert_infers(tc.draw(gen::lambda_expr()));
}

/// Full recursive generation.
#[hegel::test(test_cases = 256)]
fn test_recursive_typing(tc: TestCase) {
    const DEPTH: u32 = 5;
    assert_infers_modulo_unions(tc.draw(gen::nix_texts(DEPTH)));
}

/// Type-directed generation: draw a type, emit source for it, infer it back.
#[hegel::test(test_cases = 256)]
fn test_type_directed_typing(tc: TestCase) {
    assert_infers_modulo_unions(gen::nix_text_from_ty(&tc));
}

/// Deep recursive + type-directed + focused union generators.
#[hegel::test(test_cases = 64)]
fn test_combined_typing(tc: TestCase) {
    assert_infers_modulo_unions(tc.draw(gen::combined()));
}

// ==============================================================================
// Union type PBT
// ==============================================================================

#[track_caller]
fn assert_infers_union((ty, text): (RawTy, NixTextStr)) {
    let root_ty = get_inferred_root(&text);
    let expected = raw_to_root(&ty.normalize_vars()).normalize_set_ops();
    assert_eq!(
        root_ty.normalize_vars().normalize_set_ops(),
        expected,
        "source: {text}"
    );
}

/// Two distinct primitives in if-then-else produce the expected 2-member union.
#[hegel::test(test_cases = 256)]
fn test_union_prim_if_else(tc: TestCase) {
    assert_infers_union(gen::union_prim_if_else(&tc));
}

/// Three distinct primitives in nested if-then-else produce a 3-member union.
#[hegel::test(test_cases = 256)]
fn test_union_three_way(tc: TestCase) {
    assert_infers_union(gen::union_three_way(&tc));
}

// ==============================================================================
// Intersection type PBT
// ==============================================================================
//
// Intersection types can't be generated in positive position directly. These
// tests focus on crash freedom with intersection-producing patterns (|| narrowing,
// contradictions) and correctness of has-field conjunction.

/// Two distinct narrowing predicates.
fn distinct_predicates(tc: &TestCase, table: &[&'static str]) -> (&'static str, &'static str) {
    let (a, b) = distinct_pair(tc, table.len());
    (table[a], table[b])
}

/// `x: if builtins.<pred1> x || builtins.<pred2> x then 0 else x` — the
/// else-branch param type gets `~pred1 & ~pred2` (intersection of negations).
/// Inference doesn't panic.
#[hegel::test(test_cases = 256)]
fn test_intersection_param_crash_freedom(tc: TestCase) {
    let (pred1, pred2) = distinct_predicates(&tc, NARROWING_PREDICATES);
    let text = format!(
        "{NARROW_VAR}: if builtins.{pred1} {NARROW_VAR} || builtins.{pred2} {NARROW_VAR} \
         then 0 else {NARROW_VAR}"
    );
    let _ = check_str(&text);
}

/// `x: if x ? a && x ? b then x.a + x.b else 0` with 2-3 distinct fields:
/// the lambda body is `int`.
#[hegel::test(test_cases = 256)]
fn test_hasfield_conjunction_typing(tc: TestCase) {
    let fields = unique_idents(&tc, 2, 3);
    let conds: Vec<_> = fields
        .iter()
        .map(|f| format!("{NARROW_VAR} ? {f}"))
        .collect();
    let accesses: Vec<_> = fields.iter().map(|f| format!("{NARROW_VAR}.{f}")).collect();
    let text = format!(
        "{NARROW_VAR}: if {} then ({}) else 0",
        conds.join(" && "),
        accesses.join(" + ")
    );

    let root_ty = get_inferred_root(&text);
    let OutputTy::Lambda { body, .. } = root_ty.output_ty() else {
        panic!("expected lambda, got: {root_ty}");
    };
    assert_eq!(
        &root_ty.arena[*body],
        &OutputTy::Primitive(PrimitiveTy::Int)
    );
}

/// Contradictory narrowing (`isString` then `isInt` → Bottom) doesn't panic.
#[hegel::test(test_cases = 256)]
fn test_intersection_contradiction_crash_freedom(tc: TestCase) {
    let (pred1, pred2) = distinct_predicates(&tc, NARROWING_PREDICATES);
    let text = format!(
        "{NARROW_VAR}: if builtins.{pred1} {NARROW_VAR} \
         then (if builtins.{pred2} {NARROW_VAR} then {NARROW_VAR} else 0) \
         else 0"
    );
    let _ = check_str(&text);
}

// ==============================================================================
// Optional fields PBT
// ==============================================================================
//
// Lambda patterns with a mix of required and optional (defaulted) fields,
// applied to attrsets that may omit the optional fields. The body sums all
// fields with `+`, so the expected type is `Int`.

#[derive(Clone, Copy)]
enum CallSite {
    RequiredOnly,
    AllFields,
}

fn optional_field_src(tc: &TestCase, call_site: CallSite) -> NixTextStr {
    const MAX_EACH: usize = 3;
    let n_req = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(MAX_EACH),
    );
    let n_opt = tc.draw(
        generators::integers::<usize>()
            .min_value(1)
            .max_value(MAX_EACH),
    );
    let names = unique_idents(tc, n_req + n_opt, n_req + n_opt);
    let (req, opt) = names.split_at(n_req);

    let mut pat_parts: Vec<String> = req.iter().map(|n| n.to_string()).collect();
    pat_parts.extend(opt.iter().map(|n| format!("{n} ? 0")));
    let pattern = pat_parts.join(", ");

    let all_fields: Vec<String> = names.iter().map(|n| n.to_string()).collect();
    let body = all_fields.join(" + ");

    let provided: &[SmolStr] = match call_site {
        CallSite::RequiredOnly => req,
        CallSite::AllFields => &names,
    };
    let call_fields: Vec<String> = provided.iter().map(|n| format!("{n} = 0;")).collect();

    format!("({{ {pattern} }}: {body}) {{ {} }}", call_fields.join(" "))
}

#[track_caller]
fn assert_infers_int(text: &str) {
    let root_ty = get_inferred_root(text);
    let expected = raw_to_root(&RawTy::Primitive(PrimitiveTy::Int));
    assert_eq!(root_ty, expected, "source: {text}");
}

/// Optional fields omitted: inference succeeds and returns Int.
#[hegel::test(test_cases = 256)]
fn test_optional_field_typing(tc: TestCase) {
    assert_infers_int(&optional_field_src(&tc, CallSite::RequiredOnly));
}

/// Optional fields provided: inference also succeeds and returns Int.
#[hegel::test(test_cases = 256)]
fn test_optional_field_all_provided(tc: TestCase) {
    assert_infers_int(&optional_field_src(&tc, CallSite::AllFields));
}

// ==============================================================================
// Narrowing PBT
// ==============================================================================
//
// If-then-else expressions with type-predicate guards: narrowing must not
// crash on arbitrary combinations of guards and values.

/// The type predicates available for narrowing, paired with their builtin names.
const NARROWING_PREDICATES: &[&str] = &["isNull", "isString", "isInt", "isFloat", "isBool"];

/// All primitive type predicates (extends NARROWING_PREDICATES with isPath).
const ALL_PRIMITIVE_PREDICATES: &[&str] =
    &["isNull", "isString", "isInt", "isFloat", "isBool", "isPath"];

/// Compound predicates (then-branch only narrowing, no negation support).
const COMPOUND_PREDICATES: &[&str] = &["isAttrs", "isList", "isFunction"];

/// Predicate + operation that's valid after narrowing to that type.
const NARROWED_OPERATIONS: &[(&str, &str)] = &[
    ("isString", r#"__narr_x + "!""#),
    ("isInt", "__narr_x + 1"),
    ("isFloat", "__narr_x + 1.0"),
    ("isBool", "__narr_x && true"),
    ("isAttrs", "__narr_x.name"),
    ("isList", "builtins.head __narr_x"),
    ("isFunction", "__narr_x 42"),
];

/// Literals for equality-guard narrowing.
const EQUALITY_LITERALS: &[&str] = &["null", "true", "false", "42", r#""hello""#, "1.5"];

/// A primitive value as Nix text, for use in narrowed branches.
fn narr_value(tc: &TestCase) -> (PrimitiveTy, NixTextStr) {
    match tc.draw(generators::integers::<u8>().max_value(4)) {
        0 => (PrimitiveTy::Null, "null".to_string()),
        1 => (PrimitiveTy::Bool, "true".to_string()),
        2 => (
            PrimitiveTy::Int,
            tc.draw(generators::integers::<i32>()).to_string(),
        ),
        3 => {
            let f = tc.draw(generators::floats::<f64>().min_value(-1.0).max_value(2.0));
            (PrimitiveTy::Float, format!("{f:.4}"))
        }
        _ => (PrimitiveTy::String, format!("''{}''", tc.draw(idents()))),
    }
}

fn narr_text(tc: &TestCase) -> NixTextStr {
    narr_value(tc).1
}

fn pick<'a>(tc: &TestCase, table: &[&'a str]) -> &'a str {
    table[index(tc, table.len())]
}

/// C1: `x: if <pred> x then <val1> else <val2>` with random predicate and
/// branch values never panics (type mismatches are fine).
#[hegel::test(test_cases = 256)]
fn test_narrowing_no_crash(tc: TestCase) {
    let pred = pick(&tc, NARROWING_PREDICATES);
    let (val1, val2) = (narr_text(&tc), narr_text(&tc));
    let text = format!("{NARROW_VAR}: if {pred} {NARROW_VAR} then {val1} else {val2}");
    let _ = check_str(&text);
}

/// C2: both branches return the same primitive, so the result is that
/// primitive regardless of which predicate is used.
#[hegel::test(test_cases = 256)]
fn test_narrowing_same_type_branches(tc: TestCase) {
    let pred = pick(&tc, NARROWING_PREDICATES);
    let (prim, val) = narr_value(&tc);
    // Parenthesize the argument to avoid `-1` being parsed as subtraction.
    let text =
        format!("(({NARROW_VAR}: if {pred} {NARROW_VAR} then ({val}) else ({val})) ({val}))");
    let root_ty = get_inferred_root(&text);
    let expected = raw_to_root(&RawTy::Primitive(prim));
    assert_eq!(root_ty, expected, "source: {text}");
}

// ==============================================================================
// F1: Early-canonicalization stability — polymorphic let-binding type is stable
// regardless of how many use sites call it with different concrete types.
// ==============================================================================

/// Fixed set of polymorphic bindings and their expected canonical types.
/// Each entry is (binding_body, expected_root_type_when_returned).
const POLY_BINDINGS: &[(&str, &str)] = &[
    ("x: x", "a -> a"),
    ("x: [x]", "a -> [a]"),
    ("x: { val = x; }", "a -> { val: a }"),
    ("x: y: x", "a -> b -> a"),
];

/// Concrete values to use as arguments at use sites.
const USE_SITE_ARGS: &[&str] = &["1", "\"hello\"", "true", "3.14", "null"];

/// `let f = x: x; in f` and `let f = x: x; _u0 = f 1; _u1 = f "hi"; in f`
/// must both give `f` the same type.
#[hegel::test(test_cases = 256)]
fn test_early_canon_stability(tc: TestCase) {
    const MAX_USES: usize = 5;
    let (binding_body, _expected) = POLY_BINDINGS[index(&tc, POLY_BINDINGS.len())];
    let num_uses = tc.draw(generators::integers::<usize>().max_value(MAX_USES));

    let mut let_bindings = format!("let f = {binding_body};");
    for i in 0..num_uses {
        let arg = pick(&tc, USE_SITE_ARGS);
        let _ = std::fmt::Write::write_fmt(&mut let_bindings, format_args!(" _u{i} = f ({arg});"));
    }
    let_bindings.push_str(" in f");

    let base_nix = format!("let f = {binding_body}; in f");
    let base_ty = get_inferred_root(&base_nix);
    let actual_ty = get_inferred_root(&let_bindings);
    assert_eq!(
        base_ty, actual_ty,
        "Binding `{binding_body}` with use sites changed type:\n  base: {base_ty}\n  with uses: {actual_ty}"
    );
}

// ==============================================================================
// Complex Narrowing PBT
// ==============================================================================
//
// Literal equality guards, logical combinators (&&, ||, !), nested narrowing,
// hasField, assert, compound predicates, and multi-variable narrowing.

const GUARD_DEPTH: u32 = 2;

fn has_field_guard(tc: &TestCase, field: &SmolStr) -> NixTextStr {
    if tc.draw(generators::booleans()) {
        format!("{NARROW_VAR} ? {field}")
    } else {
        format!("builtins.hasAttr \"{field}\" {NARROW_VAR}")
    }
}

/// Recursive guard condition on `__narr_x`. Leaves: type predicates,
/// compound predicates, literal equality, hasField. Nodes: negation, and, or.
fn guard_condition(tc: &TestCase, depth: u32) -> NixTextStr {
    if depth == 0 || tc.draw(generators::booleans()) {
        return match tc.draw(generators::integers::<u8>().max_value(3)) {
            0 => format!(
                "builtins.{} {NARROW_VAR}",
                pick(tc, ALL_PRIMITIVE_PREDICATES)
            ),
            1 => format!("builtins.{} {NARROW_VAR}", pick(tc, COMPOUND_PREDICATES)),
            2 => {
                let lit = pick(tc, EQUALITY_LITERALS);
                if tc.draw(generators::booleans()) {
                    format!("{lit} == {NARROW_VAR}")
                } else {
                    format!("{NARROW_VAR} == {lit}")
                }
            }
            _ => has_field_guard(tc, &tc.draw(idents())),
        };
    }
    match tc.draw(generators::integers::<u8>().max_value(2)) {
        0 => format!("(!({}))  ", guard_condition(tc, depth - 1)),
        1 => format!(
            "(({}) && ({}))",
            guard_condition(tc, depth - 1),
            guard_condition(tc, depth - 1)
        ),
        _ => format!(
            "(({}) || ({}))",
            guard_condition(tc, depth - 1),
            guard_condition(tc, depth - 1)
        ),
    }
}

// -- Crash-freedom tests: inference must not panic, type errors are OK --------

/// Arbitrary guard combinator tree with random branch values.
#[hegel::test(test_cases = 256)]
fn test_narrowing_complex_crash_freedom(tc: TestCase) {
    let guard = guard_condition(&tc, GUARD_DEPTH);
    let (v1, v2) = (narr_text(&tc), narr_text(&tc));
    let _ = check_str(&format!("{NARROW_VAR}: if {guard} then {v1} else {v2}"));
}

/// Two levels of predicates on the same variable (possibly contradictory).
#[hegel::test(test_cases = 256)]
fn test_narrowing_nested_crash_freedom(tc: TestCase) {
    let pred1 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let pred2 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let (v1, v2, v3) = (narr_text(&tc), narr_text(&tc), narr_text(&tc));
    let _ = check_str(&format!(
        "{NARROW_VAR}: if builtins.{pred1} {NARROW_VAR} \
         then (if builtins.{pred2} {NARROW_VAR} then {v1} else {v2}) \
         else {v3}"
    ));
}

/// Two variables combined with `&&`.
#[hegel::test(test_cases = 256)]
fn test_narrowing_multi_var_crash_freedom(tc: TestCase) {
    let pred1 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let pred2 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let (v1, v2) = (narr_text(&tc), narr_text(&tc));
    let _ = check_str(&format!(
        "{NARROW_VAR}: __narr_y: \
         if builtins.{pred1} {NARROW_VAR} && builtins.{pred2} __narr_y \
         then {v1} else {v2}"
    ));
}

/// Literal equality with random orientation and op (==, !=).
#[hegel::test(test_cases = 256)]
fn test_narrowing_literal_eq_crash_freedom(tc: TestCase) {
    let lit = pick(&tc, EQUALITY_LITERALS);
    let flip = tc.draw(generators::booleans());
    let op = if tc.draw(generators::booleans()) {
        "!="
    } else {
        "=="
    };
    let (v1, v2) = (narr_text(&tc), narr_text(&tc));
    let cond = if flip {
        format!("{lit} {op} {NARROW_VAR}")
    } else {
        format!("{NARROW_VAR} {op} {lit}")
    };
    let _ = check_str(&format!("{NARROW_VAR}: if {cond} then {v1} else {v2}"));
}

/// `||` combining two predicates on the same variable.
#[hegel::test(test_cases = 256)]
fn test_narrowing_or_crash_freedom(tc: TestCase) {
    let pred1 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let pred2 = pick(&tc, ALL_PRIMITIVE_PREDICATES);
    let (v1, v2) = (narr_text(&tc), narr_text(&tc));
    let _ = check_str(&format!(
        "{NARROW_VAR}: \
         if builtins.{pred1} {NARROW_VAR} || builtins.{pred2} {NARROW_VAR} \
         then {v1} else {v2}"
    ));
}

// -- Correctness tests: inference must succeed without type errors -------------

fn narrowed_operation(tc: &TestCase) -> (&'static str, &'static str) {
    NARROWED_OPERATIONS[index(tc, NARROWED_OPERATIONS.len())]
}

/// After narrowing to type T via a predicate, T-specific operations succeed.
#[hegel::test(test_cases = 256)]
fn test_narrowing_enables_operation(tc: TestCase) {
    let (pred, operation) = narrowed_operation(&tc);
    let _ = get_inferred_root(&format!(
        "{NARROW_VAR}: if builtins.{pred} {NARROW_VAR} then ({operation}) else 0"
    ));
}

/// After `x ? name` or `builtins.hasAttr`, `x.name` access succeeds.
#[hegel::test(test_cases = 256)]
fn test_narrowing_hasfield_enables_access(tc: TestCase) {
    let field = tc.draw(idents());
    let cond = has_field_guard(&tc, &field);
    let _ = get_inferred_root(&format!(
        "{NARROW_VAR}: if {cond} then {NARROW_VAR}.{field} else \"default\""
    ));
}

/// `!pred` puts narrowing in the else-branch.
#[hegel::test(test_cases = 256)]
fn test_narrowing_negated_enables_operation(tc: TestCase) {
    let (pred, operation) = narrowed_operation(&tc);
    let _ = get_inferred_root(&format!(
        "{NARROW_VAR}: if !(builtins.{pred} {NARROW_VAR}) then 0 else ({operation})"
    ));
}

/// `assert pred; op` narrows the variable for the continuation.
#[hegel::test(test_cases = 256)]
fn test_narrowing_assert_enables_operation(tc: TestCase) {
    let (pred, operation) = narrowed_operation(&tc);
    let _ = get_inferred_root(&format!(
        "{NARROW_VAR}: assert builtins.{pred} {NARROW_VAR}; ({operation})"
    ));
}

// ==============================================================================
// Annotation Provenance Stability PBT
// ==============================================================================
//
// Type alias annotations on names (via `# type: x :: Alias`) must survive
// inference and appear consistently in both name_ty_map and expr_ty_map at
// every usage site. This catches provenance loss through extrusion,
// constraint propagation, and canonicalization.

/// Stubs defining type aliases with union types (forces the Variable branch
/// of extrude) and plain attrset types (goes through the Concrete branch).
const ANNOTATION_STUBS: &str = r#"
type Nullable = int | null;
type StringOrInt = string | int;
type Config = { enable: bool, name: string, ... };
module pkgset {
    val build :: ({ name: string, ... } | { pname: string, ... }) -> { name: string, ... };
    val lib :: Config;
}
"#;

static ANNOTATION_REGISTRY: std::sync::LazyLock<TypeAliasRegistry> =
    std::sync::LazyLock::new(|| {
        let file =
            comment_parser::parse_tix_file(ANNOTATION_STUBS).expect("parse annotation stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);
        registry
    });

/// Type aliases available for annotation tests. Each entry is
/// (alias_name, is_union_type). Union types trigger the annotation-skip
/// path in `apply_type_annotation`, which adds a Named lower bound
/// without constraining to a concrete type.
const ANNOTATION_ALIASES: &[(&str, bool)] = &[
    ("Nullable", true),
    ("StringOrInt", true),
    ("Config", false),
    // Module type with nested union in a field's type (build :: ({...} | {...}) -> {...}).
    // The alias itself is an attrset, not a union, but contains_union_resolving
    // recurses into field types and detects the union — exercising the fix.
    ("Pkgset", false),
];

/// Usage patterns for an annotated let-binding `x`.
#[derive(Debug, Clone, Copy)]
enum AnnotationUsagePattern {
    /// `let x = f; in x` — direct return of annotated binding
    DirectReturn,
    /// `let x = f; y = x; in y` — let-rebinding of annotated name
    LetRebind,
    /// `let x = f; in { inherit x; }` — inherit usage
    Inherit,
}

const ALL_USAGE_PATTERNS: &[AnnotationUsagePattern] = &[
    AnnotationUsagePattern::DirectReturn,
    AnnotationUsagePattern::LetRebind,
    AnnotationUsagePattern::Inherit,
];

fn annotation_alias(tc: &TestCase) -> (&'static str, bool) {
    ANNOTATION_ALIASES[index(tc, ANNOTATION_ALIASES.len())]
}

/// Nix source with an annotated let-binding and a usage pattern.
/// Returns (alias_name, nix_source).
fn annotation_usage(tc: &TestCase) -> (String, String) {
    let (alias_name, _is_union) = annotation_alias(tc);
    let pattern = ALL_USAGE_PATTERNS[index(tc, ALL_USAGE_PATTERNS.len())];

    let nix_src = match pattern {
        AnnotationUsagePattern::DirectReturn => {
            format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\nin x")
        }
        AnnotationUsagePattern::LetRebind => {
            format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\n  y = x;\nin y")
        }
        AnnotationUsagePattern::Inherit => {
            format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\nin {{ inherit x; }}")
        }
    };
    (alias_name.to_string(), nix_src)
}

/// Multiple usage sites of the same annotated binding:
/// `let x = f; _u0 = x; _u1 = x; in x` with 2-3 references.
fn annotation_multi_usage(tc: &TestCase) -> (String, String) {
    let (alias_name, _) = annotation_alias(tc);
    let num_uses = tc.draw(generators::integers::<usize>().min_value(2).max_value(3));

    let mut bindings = format!("f:\nlet\n  # type: x :: {alias_name}\n  x = f;\n");
    for i in 0..num_uses {
        let _ = std::fmt::Write::write_fmt(&mut bindings, format_args!("  _u{i} = x;\n"));
    }
    bindings.push_str("in x");
    (alias_name.to_string(), bindings)
}

/// Usage patterns for a pattern-field annotated parameter `pkgs`.
#[derive(Debug, Clone, Copy)]
enum PatFieldUsagePattern {
    /// `{ pkgs, ... }: pkgs` — direct return
    DirectReturn,
    /// `{ pkgs, ... }: let y = pkgs; in y` — let-rebinding
    LetRebind,
    /// `{ pkgs, ... }: pkgs.name` — field access
    FieldAccess,
    /// `{ pkgs, ... }: { inherit pkgs; }` — inherit
    Inherit,
}

const ALL_PAT_FIELD_PATTERNS: &[PatFieldUsagePattern] = &[
    PatFieldUsagePattern::DirectReturn,
    PatFieldUsagePattern::LetRebind,
    PatFieldUsagePattern::FieldAccess,
    PatFieldUsagePattern::Inherit,
];

/// Nix source with `# type: pkgs :: Alias` on a pattern field and a usage
/// of `pkgs` in the body. Returns (alias_name, nix_source).
///
/// FieldAccess is excluded for union aliases (Nullable, StringOrInt):
/// accessing `.name` on `int | null` is a genuine type error.
fn pat_field_annotation(tc: &TestCase) -> (String, String) {
    let (alias_name, is_union) = annotation_alias(tc);
    let candidates: Vec<PatFieldUsagePattern> = ALL_PAT_FIELD_PATTERNS
        .iter()
        .copied()
        .filter(|p| !(is_union && matches!(p, PatFieldUsagePattern::FieldAccess)))
        .collect();
    let pattern = candidates[index(tc, candidates.len())];

    let header = format!("{{\n  # type: pkgs :: {alias_name}\n  pkgs,\n  ...\n}}:");
    let body = match pattern {
        PatFieldUsagePattern::DirectReturn => " pkgs",
        PatFieldUsagePattern::LetRebind => "\nlet y = pkgs; in y",
        PatFieldUsagePattern::FieldAccess => "\npkgs.name",
        PatFieldUsagePattern::Inherit => "\n{ inherit pkgs; }",
    };
    (alias_name.to_string(), format!("{header}{body}"))
}

/// Debug-formatted `expr_ty_map` entries for every `Expr::Reference` to `name`.
fn reference_types(
    module: &lang_ast::Module,
    inference: &crate::InferenceResult,
    name: &str,
) -> Vec<String> {
    module
        .exprs()
        .filter_map(|(expr_id, expr)| match expr {
            Expr::Reference(n) if n == name => inference
                .expr_ty_map
                .get(expr_id)
                .map(|ty| format!("{:?}", inference.arena[*ty])),
            _ => None,
        })
        .collect()
}

fn is_named(ty_str: &str, alias_name: &str) -> bool {
    ty_str.contains("Named") && ty_str.contains(alias_name)
}

/// Pattern field annotation: every reference to a pattern-field annotated
/// parameter shows Named(alias, ...). Exercises the
/// pre_apply_entry_lambda_annotations path.
#[hegel::test(test_cases = 256)]
fn test_annotation_pat_field_usage_named(tc: TestCase) {
    let (alias_name, nix_src) = pat_field_annotation(&tc);
    let (module, inference) = check_str_with_aliases(&nix_src, &ANNOTATION_REGISTRY);
    let inference = inference.expect("should not produce a type error");

    let ref_types = reference_types(&module, &inference, "pkgs");
    assert!(
        !ref_types.is_empty(),
        "should find at least one reference to `pkgs`"
    );
    for ty_str in &ref_types {
        assert!(
            is_named(ty_str, &alias_name),
            "reference to `pkgs` should be Named(\"{alias_name}\", ...), got: {ref_types:?}"
        );
    }
}

/// If name_ty_map contains a Named wrapper for an annotated binding, it
/// references the correct alias. Union-annotated types may show TyVar in
/// name_ty_map because early canonical snapshots see no concrete bounds, so
/// Named is only guaranteed for non-union aliases.
#[hegel::test(test_cases = 256)]
fn test_annotation_definition_named(tc: TestCase) {
    let (alias_name, nix_src) = annotation_usage(&tc);
    let (module, inference) = check_str_with_aliases(&nix_src, &ANNOTATION_REGISTRY);
    let inference = inference.expect("should not produce a type error");

    let x_name_types: Vec<_> = module
        .names()
        .filter(|(_, name)| name.text == "x")
        .filter_map(|(name_id, _)| inference.name_ty_map.get(name_id))
        .map(|ty| format!("{:?}", inference.arena[*ty]))
        .collect();

    assert!(
        !x_name_types.is_empty(),
        "should find name `x` in name_ty_map"
    );
    for ty_str in &x_name_types {
        if ty_str.contains("Named") {
            assert!(
                ty_str.contains(&alias_name),
                "definition of `x` has Named but wrong alias, expected \"{alias_name}\", got: {ty_str}"
            );
        }
    }
}

/// Every reference to an annotated name shows Named(alias, ...). For union
/// aliases the Named wrapper may not propagate through constrain_equal, so
/// only non-union aliases are checked.
#[hegel::test(test_cases = 256)]
fn test_annotation_usage_site_named(tc: TestCase) {
    let (alias_name, nix_src) = annotation_usage(&tc);
    assert_references_named(&nix_src, &alias_name, 1);
}

/// When the same annotated binding is referenced N times, every reference
/// consistently shows Named(alias, ...).
#[hegel::test(test_cases = 256)]
fn test_annotation_multi_usage_stability(tc: TestCase) {
    let (alias_name, nix_src) = annotation_multi_usage(&tc);
    assert_references_named(&nix_src, &alias_name, 2);
}

#[track_caller]
fn assert_references_named(nix_src: &str, alias_name: &str, min_refs: usize) {
    let (module, inference) = check_str_with_aliases(nix_src, &ANNOTATION_REGISTRY);
    let inference = inference.expect("should not produce a type error");
    let is_union = ANNOTATION_ALIASES
        .iter()
        .any(|(n, u)| *n == alias_name && *u);

    let ref_types = reference_types(&module, &inference, "x");
    assert!(
        ref_types.len() >= min_refs,
        "should find at least {min_refs} references to `x`, found {}",
        ref_types.len()
    );
    if is_union {
        return;
    }
    for ty_str in &ref_types {
        assert!(
            is_named(ty_str, alias_name),
            "reference to `x` should be Named(\"{alias_name}\", ...), got: {ref_types:?}"
        );
    }
}
