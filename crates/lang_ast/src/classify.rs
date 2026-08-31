// ==============================================================================
// Nix File Classification
// ==============================================================================
//
// Classifies a Nix file by its structural signals (AST-only, no type inference).
// Recognizes NixOS modules, Home Manager modules, callPackage derivations,
// overlays, flakes, libraries, and plain expressions.
//
// Lives in lang_ast so both CLI and LSP can use it without depending on
// lang_check.

use rustc_hash::FxHashSet as HashSet;

use smol_str::SmolStr;

use crate::{Bindings, Expr, ExprId, Module, NameResolution};

// ==============================================================================
// Public Types
// ==============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NixFileKind {
    NixosModule,
    HomeManagerModule,
    CallPackage,
    Overlay,
    Library,
    Flake,
    PlainExpression,
}

impl std::fmt::Display for NixFileKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NixFileKind::NixosModule => write!(f, "NixOS module"),
            NixFileKind::HomeManagerModule => write!(f, "Home Manager module"),
            NixFileKind::CallPackage => write!(f, "callPackage"),
            NixFileKind::Overlay => write!(f, "overlay"),
            NixFileKind::Library => write!(f, "library"),
            NixFileKind::Flake => write!(f, "flake"),
            NixFileKind::PlainExpression => write!(f, "plain expression"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Classification {
    pub kind: NixFileKind,
    pub confidence: f32,
    /// Set when a `/** context: X */` doc comment overrides classification.
    pub explicit_context: Option<SmolStr>,
    /// Human-readable explanation of why this classification was chosen.
    pub reason: String,
}

// ==============================================================================
// Classification Algorithm
// ==============================================================================

/// Classify a Nix file by analyzing its AST structure.
///
/// Only depends on the parsed Module and NameResolution — no type inference
/// needed. Checks for explicit `/** context: X */` annotations first, then
/// scores based on lambda parameter names, body references, and attrset keys.
pub fn classify_nix_file(module: &Module, _name_res: &NameResolution) -> Classification {
    // Step 1: Check doc comments for explicit `/** context: X */`.
    if let Some(classification) = check_explicit_context(module) {
        return classification;
    }

    let entry = module.entry_expr;

    // Step 2: Analyze entry expression shape.
    match &module[entry] {
        // Pattern lambda: { config, lib, pkgs, ... }: body
        Expr::Lambda {
            pat: Some(pat),
            body,
            ..
        } => {
            let param_names: HashSet<SmolStr> = pat
                .fields
                .iter()
                .filter_map(|(name_id, _)| name_id.map(|id| module[id].text.clone()))
                .collect();
            let has_ellipsis = pat.ellipsis;

            let body_refs = collect_body_references(module, *body);
            let body_keys = collect_body_attrset_keys(module, *body);

            score_pattern_lambda(
                &param_names,
                has_ellipsis,
                &body_refs,
                &body_keys,
                module,
                *body,
            )
        }

        // Two nested plain lambdas: final: prev: { ... } → overlay
        Expr::Lambda {
            param: Some(_),
            pat: None,
            body: inner_body,
        } => {
            if let Expr::Lambda {
                param: Some(_),
                pat: None,
                body: inner_inner_body,
            } = &module[*inner_body]
            {
                // Two nested plain lambdas — strong overlay signal.
                // Check if body references suggest overlay patterns.
                let body_refs = collect_body_references(module, *inner_inner_body);
                let mut overlay_score: f32 = 8.0;

                // Overlay bodies often reference the `prev` parameter.
                if body_refs.contains("prev") || body_refs.contains("super") {
                    overlay_score += 2.0;
                }

                Classification {
                    kind: NixFileKind::Overlay,
                    confidence: overlay_score / (overlay_score + 1.0),
                    explicit_context: None,
                    reason: "two nested plain lambdas (overlay pattern)".into(),
                }
            } else {
                // Single plain lambda — likely a library function.
                Classification {
                    kind: NixFileKind::Library,
                    confidence: 0.4,
                    explicit_context: None,
                    reason: "single plain lambda".into(),
                }
            }
        }

        // Bare attrset — could be a flake or plain expression.
        Expr::AttrSet { bindings, .. } => classify_bare_attrset(module, bindings),

        // Anything else (let-in, literal, etc.) → plain expression.
        _ => Classification {
            kind: NixFileKind::PlainExpression,
            confidence: 0.8,
            explicit_context: None,
            reason: "not a lambda or attrset".into(),
        },
    }
}

// ==============================================================================
// Explicit Context Override
// ==============================================================================

/// Check doc comments for `/** context: X */` annotations.
fn check_explicit_context(module: &Module) -> Option<Classification> {
    // Check doc comments on the entry expression.
    let docs = module.type_dec_map.docs_for_expr(module.entry_expr)?;

    for doc in docs {
        let trimmed = doc.trim();
        if let Some(ctx_name) = trimmed.strip_prefix("context:") {
            let ctx_name = ctx_name.trim();
            let kind = match ctx_name {
                "nixos" => NixFileKind::NixosModule,
                "home-manager" => NixFileKind::HomeManagerModule,
                "callpackage" | "callPackage" => NixFileKind::CallPackage,
                "overlay" => NixFileKind::Overlay,
                "library" => NixFileKind::Library,
                "flake" => NixFileKind::Flake,
                _ => NixFileKind::PlainExpression,
            };
            return Some(Classification {
                kind,
                confidence: 1.0,
                explicit_context: Some(SmolStr::from(ctx_name)),
                reason: format!("explicit /** context: {ctx_name} */ annotation"),
            });
        }
    }
    None
}

// ==============================================================================
// Pattern Lambda Scoring
// ==============================================================================

/// Score contribution of one classification signal: added to the
/// (NixOS module, Home Manager module, callPackage) scores when it fires.
struct SignalWeight {
    nixos: f32,
    hm: f32,
    callpkg: f32,
}

const W_PARAM_CONFIG: SignalWeight = SignalWeight {
    nixos: 4.0,
    hm: 2.0,
    callpkg: 0.0,
};
/// osConfig is definitive for Home Manager.
const W_PARAM_OSCONFIG: SignalWeight = SignalWeight {
    nixos: 0.0,
    hm: 10.0,
    callpkg: 0.0,
};
const W_PARAM_STDENV: SignalWeight = SignalWeight {
    nixos: 0.0,
    hm: 0.0,
    callpkg: 6.0,
};
const W_PARAM_FETCHERS: SignalWeight = SignalWeight {
    nixos: 0.0,
    hm: 0.0,
    callpkg: 3.0,
};
/// config absent + pkgs/stdenv present suggests callPackage, not NixOS module.
const W_PKGS_WITHOUT_CONFIG: SignalWeight = SignalWeight {
    nixos: -3.0,
    hm: 0.0,
    callpkg: 0.0,
};
const W_BODY_MKOPTION: SignalWeight = SignalWeight {
    nixos: 4.0,
    hm: 0.0,
    callpkg: 0.0,
};
const W_BODY_MKDERIVATION: SignalWeight = SignalWeight {
    nixos: 0.0,
    hm: 0.0,
    callpkg: 5.0,
};
const W_BODY_LANG_BUILDERS: SignalWeight = SignalWeight {
    nixos: 0.0,
    hm: 0.0,
    callpkg: 4.0,
};
const W_BODY_MK_MODIFIERS: SignalWeight = SignalWeight {
    nixos: 2.0,
    hm: 2.0,
    callpkg: 0.0,
};
const W_KEY_OPTIONS: SignalWeight = SignalWeight {
    nixos: 3.0,
    hm: 0.0,
    callpkg: 0.0,
};
const W_KEY_IMPORTS: SignalWeight = SignalWeight {
    nixos: 1.0,
    hm: 1.0,
    callpkg: 0.0,
};
const W_MODULE_RETURN_SHAPE: SignalWeight = SignalWeight {
    nixos: 2.0,
    hm: 1.0,
    callpkg: 0.0,
};

/// Score a pattern-lambda file based on parameter names, body references,
/// and body attrset keys.
fn score_pattern_lambda(
    param_names: &HashSet<SmolStr>,
    _has_ellipsis: bool,
    body_refs: &HashSet<SmolStr>,
    body_keys: &HashSet<SmolStr>,
    module: &Module,
    body: ExprId,
) -> Classification {
    let mut nixos_score: f32 = 0.0;
    let mut hm_score: f32 = 0.0;
    let mut callpkg_score: f32 = 0.0;

    let mut apply = |fires: bool, w: &SignalWeight| {
        if fires {
            nixos_score += w.nixos;
            hm_score += w.hm;
            callpkg_score += w.callpkg;
        }
    };

    // ---- Parameter name scoring ----
    // lib is common across all module types but doesn't help disambiguate.
    apply(param_names.contains("config"), &W_PARAM_CONFIG);
    apply(param_names.contains("osConfig"), &W_PARAM_OSCONFIG);
    apply(param_names.contains("stdenv"), &W_PARAM_STDENV);
    apply(
        param_names.contains("fetchFromGitHub") || param_names.contains("fetchurl"),
        &W_PARAM_FETCHERS,
    );
    apply(
        !param_names.contains("config")
            && (param_names.contains("pkgs") || param_names.contains("stdenv")),
        &W_PKGS_WITHOUT_CONFIG,
    );

    // ---- Body reference scoring ----
    apply(
        body_refs.contains("mkOption") || body_refs.contains("mkEnableOption"),
        &W_BODY_MKOPTION,
    );
    apply(body_refs.contains("mkDerivation"), &W_BODY_MKDERIVATION);
    apply(
        body_refs.contains("buildPythonPackage")
            || body_refs.contains("buildGoModule")
            || body_refs.contains("buildRustPackage"),
        &W_BODY_LANG_BUILDERS,
    );
    apply(
        body_refs.contains("mkIf")
            || body_refs.contains("mkDefault")
            || body_refs.contains("mkForce"),
        &W_BODY_MK_MODIFIERS,
    );

    // ---- Body attrset key scoring ----
    apply(body_keys.contains("options"), &W_KEY_OPTIONS);
    apply(body_keys.contains("imports"), &W_KEY_IMPORTS);

    // ---- `{ options, config, ... }` return shape (NixOS module convention) ----
    // A NixOS module typically returns an attrset with `options` and/or
    // `config` keys, or is wrapped in mkMerge / mkIf.
    apply(is_module_return_shape(module, body), &W_MODULE_RETURN_SHAPE);

    // ---- Pick the winner ----
    let scores = [
        (NixFileKind::NixosModule, nixos_score),
        (NixFileKind::HomeManagerModule, hm_score),
        (NixFileKind::CallPackage, callpkg_score),
    ];

    let (best_kind, best_score) = scores
        .iter()
        .copied()
        .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
        .unwrap();

    let second_score = scores
        .iter()
        .filter(|(k, _)| *k != best_kind)
        .map(|(_, s)| *s)
        .fold(0.0_f32, f32::max);

    // If best score is <= 0, classify as Library (pattern lambda without strong signals).
    if best_score <= 0.0 {
        return Classification {
            kind: NixFileKind::Library,
            confidence: 0.3,
            explicit_context: None,
            reason: "pattern lambda with no strong classification signals".into(),
        };
    }

    let confidence = best_score / (best_score + second_score + 1.0);

    let reason =
        format!("scores: nixos={nixos_score:.0}, hm={hm_score:.0}, callpkg={callpkg_score:.0}");

    Classification {
        kind: best_kind,
        confidence,
        explicit_context: None,
        reason,
    }
}

// ==============================================================================
// Bare Attrset Classification
// ==============================================================================

/// Classify a bare attrset (not inside a lambda).
fn classify_bare_attrset(module: &Module, bindings: &Bindings) -> Classification {
    let keys: HashSet<SmolStr> = bindings
        .statics
        .iter()
        .map(|(name_id, _)| module[*name_id].text.clone())
        .collect();

    // Flake detection: must have both `inputs` and `outputs`.
    if keys.contains("inputs") && keys.contains("outputs") {
        return Classification {
            kind: NixFileKind::Flake,
            confidence: 0.95,
            explicit_context: None,
            reason: "bare attrset with `inputs` and `outputs` keys".into(),
        };
    }

    Classification {
        kind: NixFileKind::PlainExpression,
        confidence: 0.7,
        explicit_context: None,
        reason: "bare attrset without flake keys".into(),
    }
}

// ==============================================================================
// Helpers: Body Analysis
// ==============================================================================

/// Collect reference names and select-chain leaf names from a body expression.
/// Stops at nested Lambda boundaries to avoid inner-scope pollution.
fn collect_body_references(module: &Module, body: ExprId) -> HashSet<SmolStr> {
    let mut refs = HashSet::default();
    let mut stack = vec![body];

    while let Some(expr_id) = stack.pop() {
        match &module[expr_id] {
            // Don't descend into nested lambdas.
            Expr::Lambda { .. } => continue,

            Expr::Reference(name) => {
                refs.insert(name.clone());
            }

            // For select chains like `stdenv.mkDerivation`, collect the leaf name.
            Expr::Select { set, attrpath, .. } => {
                // Collect the leaf attribute name(s).
                for &attr_expr in attrpath.iter() {
                    if let Expr::Literal(crate::Literal::String(s)) = &module[attr_expr] {
                        refs.insert(s.clone());
                    }
                }
                // Also walk the set expression (to pick up the base reference).
                stack.push(*set);
                // Walk default_expr if present.
                if let Expr::Select {
                    default_expr: Some(def),
                    ..
                } = &module[expr_id]
                {
                    stack.push(*def);
                }
                continue; // Already handled children manually.
            }

            other => {
                other.walk_child_exprs(|child| stack.push(child));
            }
        }
    }

    refs
}

/// Collect top-level attrset keys from the body expression.
/// If body is a let-in, looks at the inner body. If body is an attrset,
/// collects its static key names.
fn collect_body_attrset_keys(module: &Module, body: ExprId) -> HashSet<SmolStr> {
    let mut keys = HashSet::default();
    let target = unwrap_let_in(module, body);

    if let Expr::AttrSet { bindings, .. } = &module[target] {
        for (name_id, _) in bindings.statics.iter() {
            keys.insert(module[*name_id].text.clone());
        }
    }

    keys
}

/// Unwrap nested let-in expressions to find the inner body.
fn unwrap_let_in(module: &Module, expr: ExprId) -> ExprId {
    let mut current = expr;
    loop {
        match &module[current] {
            Expr::LetIn { body, .. } => current = *body,
            _ => return current,
        }
    }
}

/// Check if the body expression looks like a NixOS/HM module return shape:
/// typically an attrset with keys like `options`, `config`, `imports`, `meta`.
fn is_module_return_shape(module: &Module, body: ExprId) -> bool {
    let target = unwrap_let_in(module, body);
    if let Expr::AttrSet { bindings, .. } = &module[target] {
        let keys: HashSet<SmolStr> = bindings
            .statics
            .iter()
            .map(|(name_id, _)| module[*name_id].text.clone())
            .collect();
        keys.contains("options") || (keys.contains("config") && keys.len() <= 5)
    } else {
        false
    }
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    /// Helper: parse Nix source and classify it.
    fn classify(source: &str) -> Classification {
        let r = crate::run_syntax_pipeline(source);
        classify_nix_file(&r.module, &r.name_res)
    }

    #[test]
    fn classify_nixos_module() {
        let c = classify(
            r#"{ config, lib, pkgs, ... }: {
                options.services.foo.enable = true;
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::NixosModule);
        assert!(c.confidence > 0.5, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_callpackage() {
        let c = classify(
            r#"{ stdenv, fetchFromGitHub, ... }:
            stdenv.mkDerivation {
                pname = "foo";
                src = fetchFromGitHub { owner = "x"; repo = "y"; };
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::CallPackage);
        assert!(c.confidence > 0.5, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_overlay() {
        let c = classify(
            r#"final: prev: {
                foo = prev.bar;
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::Overlay);
        assert!(c.confidence > 0.5, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_hm_module() {
        let c = classify(
            r#"{ config, lib, pkgs, osConfig, ... }: {
                home.packages = [];
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::HomeManagerModule);
        assert!(c.confidence > 0.5, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_flake() {
        let c = classify(
            r#"{
                inputs = { nixpkgs.url = "github:NixOS/nixpkgs"; };
                outputs = { self, nixpkgs }: {};
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::Flake);
        assert!(c.confidence > 0.9, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_plain_expression() {
        let c = classify("let x = 1; in x");
        assert_eq!(c.kind, NixFileKind::PlainExpression);
    }

    #[test]
    fn classify_explicit_context_overrides() {
        let c = classify(
            r#"/** context: nixos */
            { pkgs, ... }: pkgs"#,
        );
        assert_eq!(c.kind, NixFileKind::NixosModule);
        assert_eq!(c.confidence, 1.0);
        assert_eq!(c.explicit_context, Some(SmolStr::from("nixos")));
    }

    #[test]
    fn classify_ambiguous_low_confidence() {
        // { lib, ... }: { ... } — could be anything.
        let c = classify("{ lib, ... }: { }");
        // Should classify as Library (no strong signals) with low confidence.
        assert!(
            c.confidence < 0.5,
            "ambiguous file should have low confidence: {} (kind={:?})",
            c.confidence,
            c.kind
        );
    }

    #[test]
    fn classify_nixos_module_with_mkoption() {
        let c = classify(
            r#"{ config, lib, pkgs, ... }: {
                options.services.myservice = {
                    enable = lib.mkEnableOption "myservice";
                    port = lib.mkOption {};
                };
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::NixosModule);
        assert!(c.confidence > 0.6, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_callpackage_with_build_helpers() {
        let c = classify(
            r#"{ lib, buildPythonPackage, fetchFromGitHub, ... }:
            buildPythonPackage {
                pname = "mypackage";
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::CallPackage);
        assert!(c.confidence > 0.5, "confidence={}", c.confidence);
    }

    #[test]
    fn classify_nixos_module_with_mkif() {
        let c = classify(
            r#"{ config, lib, pkgs, ... }:
            let cfg = config.services.foo;
            in {
                config = lib.mkIf cfg.enable {
                    systemd.services.foo = {};
                };
            }"#,
        );
        assert_eq!(c.kind, NixFileKind::NixosModule);
    }
}
