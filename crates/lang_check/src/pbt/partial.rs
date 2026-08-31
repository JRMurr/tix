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

use hegel::generators;

use super::gen::prim_src;
use crate::tests::check_str;
use lang_ty::hegel_gen::prims;

const MIN_BINDINGS: usize = 2;
const MAX_BINDINGS: usize = 4;

/// Multiple independent Nix expressions for let-bindings. Uses only
/// primitives to guarantee independent SCC groups and avoid inner names
/// (attrset fields etc.) that won't get early-canonical snapshots.
fn independent_exprs(tc: &hegel::TestCase) -> Vec<String> {
    let n = tc.draw(
        generators::integers::<usize>()
            .min_value(MIN_BINDINGS)
            .max_value(MAX_BINDINGS),
    );
    (0..n)
        .map(|_| {
            let prim = tc.draw(prims());
            prim_src(tc, prim)
        })
        .collect()
}

fn binding_name(i: usize) -> String {
    format!("_{}", (b'a' + i as u8) as char)
}

/// Partial inference of all groups should produce the same types for
/// top-level let-in bindings as full inference.
#[hegel::test(test_cases = 50)]
fn partial_matches_full_for_independent_bindings(tc: hegel::TestCase) {
    let exprs = independent_exprs(&tc);
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
        Err(_) => return,
    };

    // Partial inference
    let r = lang_ast::run_syntax_pipeline(&src);
    let n_groups = r.grouped_defs.len();

    if n_groups == 0 {
        return;
    }

    let aliases = crate::load_inline_aliases(
        std::sync::Arc::new(crate::aliases::TypeAliasRegistry::default()),
        &r.module,
    );
    let check = crate::CheckCtx::new(
        &r.module,
        &r.name_res,
        &r.module_indices.binding_expr,
        aliases,
        std::collections::HashMap::default(),
        std::sync::Arc::default(),
    );
    let (partial_result, _diags) = check.infer_prog_up_to_group(r.grouped_defs, n_groups - 1);

    // Only compare top-level let-in bindings (which get early-canonical
    // snapshots). Skip inner names that degrade under bailed_out.
    let binding_names: std::collections::HashSet<String> = (0..n).map(binding_name).collect();

    for (name_id, name_data) in r.module.names() {
        if !binding_names.contains(name_data.text.as_str()) {
            continue;
        }
        if let (Some(&partial_ty), Some(&full_ty)) = (
            partial_result.name_ty_map.get(name_id),
            full_result.name_ty_map.get(name_id),
        ) {
            let partial_display = format!("{}", partial_result.arena.display(partial_ty));
            let full_display = format!("{}", full_result.arena.display(full_ty));
            assert_eq!(
                &partial_display, &full_display,
                "type mismatch for binding '{}': partial={}, full={}",
                name_data.text, partial_display, full_display,
            );
        }
    }
}
