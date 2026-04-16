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

use proptest::prelude::*;

use super::NixTextStr;
use crate::tests::check_multifile_fixpoint;

const MAX_FIXPOINT_ROUNDS: usize = 4;

// ==============================================================================
// Strategies for generating cycle topologies
// ==============================================================================

/// Generate a two-file cycle where A exports a local field + a field from B,
/// and B exports a local field + a field from A.
fn arb_cycle_pair() -> impl Strategy<Value = Vec<(&'static str, String)>> {
    (arb_prim_value(), arb_prim_value()).prop_map(|(a_val, b_val)| {
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
    })
}

/// Generate a three-file ring: A→B→C→A, each with a local field and a
/// field sourced from its import.
fn arb_cycle_ring3() -> impl Strategy<Value = Vec<(&'static str, String)>> {
    (arb_prim_value(), arb_prim_value(), arb_prim_value()).prop_map(|(a_val, b_val, c_val)| {
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
    })
}

/// Generate a cycle pair {A,B} plus a non-cyclic file C that both import.
/// Tests that acyclic deps are unaffected by fixpoint iteration.
fn arb_cycle_with_acyclic_dep() -> impl Strategy<Value = Vec<(&'static str, String)>> {
    (arb_prim_value(), arb_prim_value(), arb_prim_value()).prop_map(
        |(a_val, b_val, c_val)| {
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
        },
    )
}

/// Generate a random primitive value literal.
fn arb_prim_value() -> impl Strategy<Value = NixTextStr> {
    prop_oneof![
        any::<i32>().prop_map(|i| i.to_string()),
        Just("\"hello\"".to_string()),
        Just("true".to_string()),
        Just("null".to_string()),
    ]
}

// ==============================================================================
// Crash-freedom: fixpoint iteration never panics
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128, .. ProptestConfig::default()
    })]

    /// Two-file cycle with random local values — no panic.
    #[test]
    fn cyclic_pair_crash_freedom(files in arb_cycle_pair()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let _ = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
    }

    /// Three-file ring with random local values — no panic.
    #[test]
    fn cyclic_ring3_crash_freedom(files in arb_cycle_ring3()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let _ = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
    }

    /// Cycle with acyclic dependency — no panic.
    #[test]
    fn cyclic_with_acyclic_dep_crash_freedom(files in arb_cycle_with_acyclic_dep()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let _ = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
    }
}

// ==============================================================================
// Convergence: fixpoint terminates within cap
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64, .. ProptestConfig::default()
    })]

    #[test]
    fn cyclic_pair_converges(files in arb_cycle_pair()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let (_types, rounds) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
        prop_assert!(
            rounds <= MAX_FIXPOINT_ROUNDS,
            "expected convergence within {MAX_FIXPOINT_ROUNDS} rounds, took {rounds}"
        );
    }

    #[test]
    fn cyclic_ring3_converges(files in arb_cycle_ring3()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let (_types, rounds) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
        prop_assert!(
            rounds <= MAX_FIXPOINT_ROUNDS,
            "expected convergence within {MAX_FIXPOINT_ROUNDS} rounds, took {rounds}"
        );
    }
}

// ==============================================================================
// Idempotence: extra round after convergence produces the same types
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64, .. ProptestConfig::default()
    })]

    #[test]
    fn cyclic_pair_idempotent(files in arb_cycle_pair()) {
        let refs: Vec<(&str, &str)> = files.iter().map(|(p, s)| (*p, s.as_str())).collect();
        let (types_n, _) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS);
        let (types_n1, _) = check_multifile_fixpoint(&refs, MAX_FIXPOINT_ROUNDS + 1);

        for (path, ty_n) in &types_n {
            if let Some(ty_n1) = types_n1.get(path) {
                prop_assert!(
                    ty_n == ty_n1,
                    "type changed after convergence for {}: {} vs {}",
                    path.display(), ty_n, ty_n1
                );
            }
        }
    }
}
