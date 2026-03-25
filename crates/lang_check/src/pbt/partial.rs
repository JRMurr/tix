// ==============================================================================
// Property-Based Tests for Partial Inference
// ==============================================================================
//
// Tests that partial inference (infer_prog_up_to_group) produces the same
// binding types as full inference for the groups it processes.
//
// Since partial inference forces bailed_out=true (to skip expr canonicalization),
// names without early-canonical snapshots may degrade to TyVar(0). We only
// compare top-level let-in bindings (which do get early-canonical snapshots)
// and skip inner names (attrset fields, lambda params, etc.).

use proptest::prelude::*;

use crate::tests::check_str;

/// Generate multiple independent Nix expressions for let-bindings.
/// Uses only primitives to guarantee independent SCC groups and avoid
/// inner names (attrset fields etc.) that won't get early-canonical snapshots.
fn arb_independent_exprs() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec(
        prop_oneof![
            Just("42".to_string()),
            Just("3.14".to_string()),
            Just("true".to_string()),
            Just("\"hello\"".to_string()),
            Just("null".to_string()),
        ],
        2..5,
    )
}

fn binding_name(i: usize) -> String {
    format!("_{}", (b'a' + i as u8) as char)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Partial inference of all groups should produce the same types for
    /// top-level let-in bindings as full inference.
    #[test]
    fn partial_matches_full_for_independent_bindings(
        exprs in arb_independent_exprs(),
    ) {
        let n = exprs.len();
        let bindings: Vec<String> = exprs
            .iter()
            .enumerate()
            .map(|(i, e)| format!("{} = {e}", binding_name(i)))
            .collect();
        let last_name = binding_name(n - 1);
        let src = format!("let {} in {last_name}", bindings.join("; "));

        // Full inference
        let (_, full_result) = check_str(&src);
        let full_result = match full_result {
            Ok(r) => r,
            Err(_) => return Ok(()),
        };

        // Partial inference
        let (db, file) = lang_ast::tests::TestDatabase::single_file(&src).unwrap();
        let module = lang_ast::module(&db, file);
        let name_res = lang_ast::name_resolution(&db, file);
        let indices = lang_ast::module_indices(&db, file);
        let groups = lang_ast::group_def(&db, file);
        let n_groups = groups.len();

        if n_groups == 0 {
            return Ok(());
        }

        let aliases = crate::load_inline_aliases(
            std::sync::Arc::new(crate::aliases::TypeAliasRegistry::default()),
            &module,
        );
        let check = crate::CheckCtx::new(
            &module,
            &name_res,
            &indices.binding_expr,
            aliases,
            std::collections::HashMap::new(),
            std::sync::Arc::default(),
        );
        let (partial_result, _diags) = check.infer_prog_up_to_group(groups, n_groups - 1);

        // Only compare top-level let-in bindings (which get early-canonical
        // snapshots). Skip inner names that degrade under bailed_out.
        let binding_names: std::collections::HashSet<String> =
            (0..n).map(|i| binding_name(i)).collect();

        for (name_id, name_data) in module.names() {
            if !binding_names.contains(name_data.text.as_str()) {
                continue;
            }
            if let (Some(&partial_ty), Some(&full_ty)) = (
                partial_result.name_ty_map.get(name_id),
                full_result.name_ty_map.get(name_id),
            ) {
                let partial_display = format!("{}", partial_result.arena.display(partial_ty));
                let full_display = format!("{}", full_result.arena.display(full_ty));
                prop_assert_eq!(
                    &partial_display,
                    &full_display,
                    "type mismatch for binding '{}': partial={}, full={}",
                    name_data.text,
                    partial_display,
                    full_display,
                );
            }
        }
    }
}
