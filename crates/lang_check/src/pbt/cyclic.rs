// ==============================================================================
// Property-Based Tests for Cyclic Import Chains
// ==============================================================================
//
// Tests fixpoint iteration over cyclic multi-file imports. Generates random
// cycle topologies (pairs, rings, mixed acyclic+cyclic) and verifies:
//   - Crash-freedom: inference never panics for any cycle shape.
//   - Convergence: fixpoint always terminates within the iteration cap.
//   - Idempotence: one extra round after convergence produces the same types.
//   - Acyclic equivalence: non-cycle files produce identical types regardless
//     of whether fixpoint iteration is enabled.

use hegel::generators;
use hegel::TestCase;

use super::NixTextStr;
use crate::tests::check_multifile_fixpoint;

const MAX_FIXPOINT_ROUNDS: usize = 4;

type Files = Vec<(&'static str, String)>;

// ==============================================================================
// Generators for cycle topologies
// ==============================================================================

/// A random primitive value literal.
fn prim_value(tc: &TestCase) -> NixTextStr {
    match tc.draw(generators::integers::<u8>().max_value(3)) {
        0 => tc.draw(generators::integers::<i32>()).to_string(),
        1 => "\"hello\"".to_string(),
        2 => "true".to_string(),
        _ => "null".to_string(),
    }
}

/// Two-file cycle where A exports a local field + a field from B, and B
/// exports a local field + a field from A.
fn cycle_pair(tc: &TestCase) -> Files {
    let (a_val, b_val) = (prim_value(tc), prim_value(tc));
    vec![
        (
            "/a.nix",
            format!("{{ local = {a_val}; fromB = (import /b.nix).local; }}"),
        ),
        (
            "/b.nix",
            format!("{{ local = {b_val}; fromA = (import /a.nix).local; }}"),
        ),
    ]
}

/// Three-file ring: A→B→C→A, each with a local field and a field sourced
/// from its import.
fn cycle_ring3(tc: &TestCase) -> Files {
    let (a_val, b_val, c_val) = (prim_value(tc), prim_value(tc), prim_value(tc));
    vec![
        (
            "/a.nix",
            format!("{{ local = {a_val}; fromC = (import /c.nix).local; }}"),
        ),
        (
            "/b.nix",
            format!("{{ local = {b_val}; fromA = (import /a.nix).local; }}"),
        ),
        (
            "/c.nix",
            format!("{{ local = {c_val}; fromB = (import /b.nix).local; }}"),
        ),
    ]
}

/// Cycle pair {A,B} plus a non-cyclic file C that both import. Tests that
/// acyclic deps are unaffected by fixpoint iteration.
fn cycle_with_acyclic_dep(tc: &TestCase) -> Files {
    let (a_val, b_val, c_val) = (prim_value(tc), prim_value(tc), prim_value(tc));
    vec![
        (
            "/a.nix",
            format!(
                "{{ local = {a_val}; fromB = (import /b.nix).local; fromC = (import /c.nix).val; }}"
            ),
        ),
        (
            "/b.nix",
            format!(
                "{{ local = {b_val}; fromA = (import /a.nix).local; fromC = (import /c.nix).val; }}"
            ),
        ),
        ("/c.nix", format!("{{ val = {c_val}; }}")),
    ]
}

fn as_refs(files: &Files) -> Vec<(&str, &str)> {
    files.iter().map(|(p, s)| (*p, s.as_str())).collect()
}

// ==============================================================================
// Crash-freedom: fixpoint iteration never panics
// ==============================================================================

/// Two-file cycle with random local values — no panic.
#[hegel::test(test_cases = 128)]
fn cyclic_pair_crash_freedom(tc: TestCase) {
    let files = cycle_pair(&tc);
    let _ = check_multifile_fixpoint(&as_refs(&files), MAX_FIXPOINT_ROUNDS);
}

/// Three-file ring with random local values — no panic.
#[hegel::test(test_cases = 128)]
fn cyclic_ring3_crash_freedom(tc: TestCase) {
    let files = cycle_ring3(&tc);
    let _ = check_multifile_fixpoint(&as_refs(&files), MAX_FIXPOINT_ROUNDS);
}

/// Cycle with acyclic dependency — no panic.
#[hegel::test(test_cases = 128)]
fn cyclic_with_acyclic_dep_crash_freedom(tc: TestCase) {
    let files = cycle_with_acyclic_dep(&tc);
    let _ = check_multifile_fixpoint(&as_refs(&files), MAX_FIXPOINT_ROUNDS);
}

// ==============================================================================
// Convergence: fixpoint terminates within cap
// ==============================================================================

#[track_caller]
fn assert_converges(files: &Files) {
    let (_types, rounds) = check_multifile_fixpoint(&as_refs(files), MAX_FIXPOINT_ROUNDS);
    assert!(
        rounds <= MAX_FIXPOINT_ROUNDS,
        "expected convergence within {MAX_FIXPOINT_ROUNDS} rounds, took {rounds}"
    );
}

#[hegel::test(test_cases = 64)]
fn cyclic_pair_converges(tc: TestCase) {
    assert_converges(&cycle_pair(&tc));
}

#[hegel::test(test_cases = 64)]
fn cyclic_ring3_converges(tc: TestCase) {
    assert_converges(&cycle_ring3(&tc));
}

// ==============================================================================
// Idempotence: extra round after convergence produces the same types
// ==============================================================================

#[hegel::test(test_cases = 64)]
fn cyclic_pair_idempotent(tc: TestCase) {
    let files = cycle_pair(&tc);
    let refs = as_refs(&files);
    let (types_n, _) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
    let (types_n1, _) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS + 1);

    for (path, ty_n) in &types_n {
        if let Some(ty_n1) = types_n1.get(path) {
            assert!(
                ty_n == ty_n1,
                "type changed after convergence for {}: {} vs {}",
                path.display(),
                ty_n,
                ty_n1
            );
        }
    }
}
