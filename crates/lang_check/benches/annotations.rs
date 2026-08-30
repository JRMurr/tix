//! Micro-benchmarks for the annotation hot paths: interning large stub
//! aliases (`intern_fresh_ty`) and extruding annotated functions at call
//! sites. Run with `cargo bench -p lang_check`.

use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_source_with_aliases;

const LIB_TIX: &str = include_str!("../../../stubs/lib.tix");
const BASIC_NIX: &str = include_str!("../../../test/basic.nix");

/// Number of call sites in `extrude_annotated_lambda`.
const CALL_SITES: usize = 50;

fn lib_registry() -> TypeAliasRegistry {
    let file = comment_parser::parse_tix_file(LIB_TIX).expect("parse lib.tix");
    let mut registry = TypeAliasRegistry::new();
    registry.load_tix_file(&file);
    registry
}

fn check(src: &str, registry: &TypeAliasRegistry) {
    let _ = divan::black_box(check_source_with_aliases(src, registry));
}

/// Interns the whole `Lib` alias from a single annotation.
#[divan::bench]
fn intern_lib_alias(bencher: divan::Bencher) {
    let registry = lib_registry();
    let src = "let /** type: lib :: Lib */ lib = null; in lib.strings.concatStringsSep";

    bencher.bench_local(|| check(src, &registry));
}

/// Many call sites of an annotated polymorphic function whose signature
/// mentions stub aliases: each call site extrudes the `Named` types.
#[divan::bench]
fn extrude_annotated_lambda(bencher: divan::Bencher) {
    let registry = lib_registry();
    let calls: String = (0..CALL_SITES)
        .map(|i| format!("(f {{ name = \"p{i}\"; }})"))
        .collect::<Vec<_>>()
        .join(" ");
    let src = format!(
        "let /** type: f :: {{ name: string, ... }} -> Derivation */ f = x: x; in [ {calls} ]"
    );

    bencher.bench_local(|| check(&src, &registry));
}

/// Recursive inline alias (GitHub #18).
#[divan::bench]
fn recursive_alias_issue_18(bencher: divan::Bencher) {
    let registry = TypeAliasRegistry::new();
    let src = r#"
# type AccessPath = [ string | { match: a, path: AccessPath } ];
rec {
  # type: countDown :: AccessPath -> int
  countDown = n: if n == [] then 0 else countDown (builtins.tail n);
}
"#;

    bencher.bench_local(|| check(src, &registry));
}

/// End-to-end on the basic fixture with lib stubs loaded.
#[divan::bench]
fn basic_fixture(bencher: divan::Bencher) {
    let registry = lib_registry();

    bencher.bench_local(|| check(BASIC_NIX, &registry));
}

fn main() {
    divan::main();
}
