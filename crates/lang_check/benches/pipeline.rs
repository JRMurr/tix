//! Benchmarks for the pipeline stages around annotation handling (which
//! `annotations.rs` covers): parsing/lowering, `.tix` parsing, output-type
//! simplification, and inference on synthetic programs that stress one
//! mechanism each. Run with `cargo bench -p lang_check`.

use std::collections::BTreeMap;

use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_source_with_aliases;
use lang_ty::simplify::simplify;
use lang_ty::{AttrSetTy, OutputTy, PrimitiveTy, TyRef, TypeArena};

const LIB_TIX: &str = include_str!("../../../stubs/lib.tix");
const STRINGS_NIX: &str = include_str!("../../../test/strings.nix");

/// Bindings / iterations in each synthetic program.
const N: usize = 200;
/// Nesting depth for the deep-nesting programs.
const DEPTH: usize = 100;
/// Alternatives in the simplified union.
const UNION_ARMS: usize = 40;

fn lib_registry() -> TypeAliasRegistry {
    let file = comment_parser::parse_tix_file(LIB_TIX).expect("parse lib.tix");
    let mut registry = TypeAliasRegistry::new();
    registry.load_tix_file(&file);
    registry
}

fn check(src: &str, registry: &TypeAliasRegistry) {
    let _ = divan::black_box(check_source_with_aliases(src, registry));
}

fn bench_src(bencher: divan::Bencher, src: String) {
    let registry = TypeAliasRegistry::new();
    bencher.bench_local(|| check(&src, &registry));
}

fn join(n: usize, f: impl Fn(usize) -> String) -> String {
    (0..n).map(f).collect::<Vec<_>>().join("\n")
}

// ------------------------------------------------------------------------------
// Front end
// ------------------------------------------------------------------------------

/// Parse + lower + name resolution + SCC grouping, no inference.
#[divan::bench]
fn syntax_pipeline_strings(bencher: divan::Bencher) {
    bencher.bench_local(|| divan::black_box(lang_ast::run_syntax_pipeline(STRINGS_NIX)));
}

/// Pest parse + collection of the shipped lib stubs.
#[divan::bench]
fn parse_lib_tix(bencher: divan::Bencher) {
    bencher.bench_local(|| divan::black_box(comment_parser::parse_tix_file(LIB_TIX)));
}

/// Loading the parsed stubs into the alias registry.
#[divan::bench]
fn load_lib_registry(bencher: divan::Bencher) {
    let file = comment_parser::parse_tix_file(LIB_TIX).expect("parse lib.tix");
    bencher.bench_local(|| {
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);
        divan::black_box(registry)
    });
}

// ------------------------------------------------------------------------------
// End to end
// ------------------------------------------------------------------------------

/// Full check of the nixpkgs `lib/strings.nix` copy with lib stubs loaded.
#[divan::bench(sample_count = 20)]
fn strings_fixture(bencher: divan::Bencher) {
    let registry = lib_registry();
    bencher.bench_local(|| check(STRINGS_NIX, &registry));
}

// ------------------------------------------------------------------------------
// Inference micro-benchmarks
// ------------------------------------------------------------------------------

/// Long chain of dependent let bindings: one SCC per binding, each
/// generalized then instantiated by the next.
#[divan::bench]
fn let_chain(bencher: divan::Bencher) {
    let binds = join(N, |i| match i {
        0 => "x0 = 1;".into(),
        _ => format!("x{i} = x{} + 1;", i - 1),
    });
    bench_src(bencher, format!("let {binds} in x{}", N - 1));
}

/// One large mutually recursive SCC.
#[divan::bench]
fn mutual_recursion_scc(bencher: divan::Bencher) {
    let binds = join(N, |i| {
        let next = (i + 1) % N;
        format!("f{i} = n: if n == 0 then 0 else f{next} (n - 1);")
    });
    bench_src(bencher, format!("let {binds} in f0 10"));
}

/// Polymorphic function instantiated at many call sites with distinct types.
#[divan::bench]
fn poly_instantiation(bencher: divan::Bencher) {
    let calls = join(N, |i| match i % 3 {
        0 => format!("(id {i})"),
        1 => format!("(id \"s{i}\")"),
        _ => format!("(id [ {i} ])"),
    });
    bench_src(bencher, format!("let id = x: x; in [ {calls} ]"));
}

/// Deferred overload resolution: a long `+` chain mixing ints and floats.
#[divan::bench]
fn overload_chain(bencher: divan::Bencher) {
    let terms = join(N, |i| {
        if i % 2 == 0 {
            format!("{i}")
        } else {
            format!("{i}.5")
        }
    });
    bench_src(bencher, terms.replace('\n', " + "));
}

/// String concatenation chain (overloaded `+` on strings).
#[divan::bench]
fn string_concat_chain(bencher: divan::Bencher) {
    let terms = join(N, |i| format!("\"s{i}\""));
    bench_src(bencher, terms.replace('\n', " + "));
}

/// Attrset merge chain: `//` on wide attrsets with overlapping fields.
#[divan::bench]
fn attrset_merge_chain(bencher: divan::Bencher) {
    let sets = join(N, |i| format!("{{ a{i} = {i}; shared = \"{i}\"; }}"));
    bench_src(bencher, sets.replace('\n', " // "));
}

/// One attrset literal with many fields, then many field selections.
#[divan::bench]
fn wide_attrset(bencher: divan::Bencher) {
    let fields = join(N, |i| format!("f{i} = {i};"));
    let selects = join(N, |i| format!("s.f{i}"));
    bench_src(
        bencher,
        format!(
            "let s = {{ {fields} }}; in [ {} ]",
            selects.replace('\n', " ")
        ),
    );
}

/// Row polymorphism: one field accessor applied to many differently shaped
/// attrsets.
#[divan::bench]
fn row_poly_calls(bencher: divan::Bencher) {
    let calls = join(N, |i| {
        format!("(get {{ name = \"n{i}\"; extra{i} = {i}; }})")
    });
    bench_src(bencher, format!("let get = s: s.name; in [ {calls} ]"));
}

/// Nested if/else narrowing on one variable.
#[divan::bench]
fn narrowing_chain(bencher: divan::Bencher) {
    let body = (0..N).rev().fold("0".to_string(), |acc, i| {
        let guard = match i % 4 {
            0 => "builtins.isString x",
            1 => "builtins.isInt x",
            2 => "x == null",
            _ => "x ? attr",
        };
        format!("if {guard} then {i} else ({acc})")
    });
    bench_src(bencher, format!("x: {body}"));
}

/// Deeply nested attrset literal, then a deep selection path.
#[divan::bench]
fn deep_attrset_nesting(bencher: divan::Bencher) {
    let lit = (0..DEPTH).fold("1".to_string(), |acc, _| format!("{{ inner = {acc}; }}"));
    let path = vec!["inner"; DEPTH].join(".");
    bench_src(bencher, format!("let s = {lit}; in s.{path}"));
}

/// Deeply nested lambdas (curried function with many parameters) applied
/// to all arguments.
#[divan::bench]
fn deep_currying(bencher: divan::Bencher) {
    let params = join(DEPTH, |i| format!("p{i}:")).replace('\n', " ");
    let args = join(DEPTH, |i| format!("{i}")).replace('\n', " ");
    bench_src(
        bencher,
        format!("let f = {params} p{}; in f {args}", DEPTH - 1),
    );
}

/// List literal of heterogeneous elements: the element type is a wide union.
#[divan::bench]
fn wide_union_list(bencher: divan::Bencher) {
    let elems = join(N, |i| match i % 4 {
        0 => format!("{i}"),
        1 => format!("\"s{i}\""),
        2 => format!("{{ k{i} = {i}; }}"),
        _ => format!("[ {i} ]"),
    });
    bench_src(bencher, format!("[ {} ]", elems.replace('\n', " ")));
}

/// `with` scoping: many references resolved through a `with` expression.
#[divan::bench]
fn with_scope_refs(bencher: divan::Bencher) {
    let fields = join(N, |i| format!("f{i} = {i};"));
    let refs = join(N, |i| format!("f{i}")).replace('\n', " ");
    bench_src(bencher, format!("with {{ {fields} }}; [ {refs} ]"));
}

// ------------------------------------------------------------------------------
// Output simplification
// ------------------------------------------------------------------------------

/// Co-occurrence simplification on a wide union of lambdas whose type
/// variables recur across arms.
#[divan::bench]
fn simplify_wide_union(bencher: divan::Bencher) {
    let mut arena = TypeArena::new();
    let ty = wide_lambda_union(&mut arena);

    bencher.bench_local(|| {
        let mut arena = arena.clone();
        divan::black_box(simplify(&mut arena, ty))
    });
}

/// `(α ∧ prim) -> { field: α | β } | ...` repeated with a rotating primitive.
fn wide_lambda_union(arena: &mut TypeArena) -> TyRef {
    const PRIMS: [PrimitiveTy; 4] = [
        PrimitiveTy::Int,
        PrimitiveTy::String,
        PrimitiveTy::Bool,
        PrimitiveTy::Float,
    ];

    let arms = (0..UNION_ARMS)
        .map(|i| {
            let var_a = arena.intern(OutputTy::TyVar(i as u32));
            let var_b = arena.intern(OutputTy::TyVar((i + 1) as u32));
            let prim = arena.intern(OutputTy::Primitive(PRIMS[i % PRIMS.len()]));
            let param = arena.intern(OutputTy::Intersection(vec![var_a, prim]));
            let field = arena.intern(OutputTy::Union(vec![var_a, var_b]));
            let fields = BTreeMap::from([("field".into(), field)]);
            let body = arena.intern(OutputTy::AttrSet(AttrSetTy::from_fields(fields)));
            arena.intern(OutputTy::Lambda { param, body })
        })
        .collect();

    arena.intern(OutputTy::Union(arms))
}

fn main() {
    divan::main();
}
