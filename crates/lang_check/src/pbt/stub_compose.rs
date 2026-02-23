// ==============================================================================
// Property-Based Tests for Stub Function Composition
// ==============================================================================
//
// Randomly picks stub-declared functions, composes them in type-valid ways,
// and tests all real-world access patterns:
//   - Top-level vals (global_vals): bare names like `id 42`
//   - Module-qualified access: `lib.id 42`, `lib.strings.toLower "X"`
//   - Lambda parameter pattern: `{ lib, ... }: lib.id 42` via context args
//   - pkgs.lib pattern: `{ pkgs, ... }: let lib = pkgs.lib; in lib.id 42`
//
// Tested both with stubs loaded (types resolve, expected output types verified)
// and without stubs (names become fresh type vars, crash-freedom verified).

use std::collections::HashMap;
use std::fmt::Write as _;

use comment_parser::ParsedTy;
use lang_ty::{OutputTy, PrimitiveTy, TyRef};
use proptest::prelude::*;
use smol_str::SmolStr;

use crate::aliases::TypeAliasRegistry;
use crate::tests::{
    check_str, check_str_with_aliases_and_context, get_inferred_root_with_aliases,
    get_inferred_root_with_aliases_and_context,
};

// ==============================================================================
// Composable Stub Declarations
// ==============================================================================
//
// A self-contained set of function declarations for testing. Includes both
// top-level `val` declarations (for bare-name access) and `module` declarations
// (for qualified access via `lib.X`, `lib.strings.X`, etc.).
//
// Deliberately uses only simple, composable signatures — no `Any`, no open
// attrsets, no `Derivation` — so we can track expected types through
// composition chains.

const COMPOSABLE_STUBS: &str = r#"
# Top-level vals for bare-name access
val id :: a -> a;
val boolToString :: bool -> string;
val toLower :: string -> string;
val toUpper :: string -> string;
val trim :: string -> string;
val stringLength :: string -> int;
val concatStrings :: [string] -> string;
val head :: [a] -> a;
val tail :: [a] -> [a];
val length :: [a] -> int;
val reverseList :: [a] -> [a];
val singleton :: a -> [a];
val range :: int -> int -> [int];

# Module structure mirroring nixpkgs lib for qualified access
module lib {
  module trivial {
    val id :: a -> a;
    val boolToString :: bool -> string;
  }
  module strings {
    val toLower :: string -> string;
    val toUpper :: string -> string;
    val trim :: string -> string;
    val stringLength :: string -> int;
    val concatStrings :: [string] -> string;
    val concatStringsSep :: string -> [string] -> string;
    val hasPrefix :: string -> string -> bool;
    val removePrefix :: string -> string -> string;
    val removeSuffix :: string -> string -> string;
    val splitString :: string -> string -> [string];
    val stringToCharacters :: string -> [string];
  }
  module lists {
    val map :: (a -> b) -> [a] -> [b];
    val filter :: (a -> bool) -> [a] -> [a];
    val head :: [a] -> a;
    val last :: [a] -> a;
    val tail :: [a] -> [a];
    val length :: [a] -> int;
    val reverseList :: [a] -> [a];
    val all :: (a -> bool) -> [a] -> bool;
    val any :: (a -> bool) -> [a] -> bool;
    val count :: (a -> bool) -> [a] -> int;
    val concatMap :: (a -> [b]) -> [a] -> [b];
    val singleton :: a -> [a];
    val unique :: [a] -> [a];
    val range :: int -> int -> [int];
    val take :: int -> [a] -> [a];
    val drop :: int -> [a] -> [a];
    val foldl :: (b -> a -> b) -> b -> [a] -> b;
    val foldr :: (a -> b -> b) -> b -> [a] -> b;
  }

  # Re-exports at lib top level (like the real lib.tix)
  val id :: a -> a;
  val boolToString :: bool -> string;
  val toLower :: string -> string;
  val toUpper :: string -> string;
  val trim :: string -> string;
  val stringLength :: string -> int;
  val concatStrings :: [string] -> string;
  val concatStringsSep :: string -> [string] -> string;
  val hasPrefix :: string -> string -> bool;
  val removePrefix :: string -> string -> string;
  val removeSuffix :: string -> string -> string;
  val splitString :: string -> string -> [string];
  val stringToCharacters :: string -> [string];
  val map :: (a -> b) -> [a] -> [b];
  val filter :: (a -> bool) -> [a] -> [a];
  val head :: [a] -> a;
  val last :: [a] -> a;
  val tail :: [a] -> [a];
  val length :: [a] -> int;
  val reverseList :: [a] -> [a];
  val singleton :: a -> [a];
  val unique :: [a] -> [a];
  val range :: int -> int -> [int];
  val take :: int -> [a] -> [a];
  val drop :: int -> [a] -> [a];
}

# pkgs module for testing { pkgs, ... }: let lib = pkgs.lib; in ...
module pkgs {
  val lib :: Lib;
}
"#;

/// Parsed once at process startup, shared by all test cases.
static COMPOSABLE_REGISTRY: std::sync::LazyLock<TypeAliasRegistry> =
    std::sync::LazyLock::new(|| {
        let file =
            comment_parser::parse_tix_file(COMPOSABLE_STUBS).expect("parse composable stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);
        registry
    });

// ==============================================================================
// Simplified Type Tracking
// ==============================================================================
//
// A flat enum for const-compatible type metadata in function tables.
// No heap allocation, so it can live in `const` arrays. List element types
// are limited to the set we actually need.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum Ty {
    Int,
    Float,
    Bool,
    String,
    Null,
    ListAny,
    ListInt,
    ListString,
    ListBool,
    ListListInt,
    /// A polymorphic type variable — any concrete type can unify here.
    Any,
}

impl Ty {
    /// Convert to OutputTy for assertion comparison.
    /// `Any` cannot be converted — it represents a type variable, not a concrete type.
    fn to_output_ty(self) -> Option<OutputTy> {
        match self {
            Ty::Int => Some(OutputTy::Primitive(PrimitiveTy::Int)),
            Ty::Float => Some(OutputTy::Primitive(PrimitiveTy::Float)),
            Ty::Bool => Some(OutputTy::Primitive(PrimitiveTy::Bool)),
            Ty::String => Some(OutputTy::Primitive(PrimitiveTy::String)),
            Ty::Null => Some(OutputTy::Primitive(PrimitiveTy::Null)),
            Ty::ListInt => Some(OutputTy::List(TyRef::from(OutputTy::Primitive(
                PrimitiveTy::Int,
            )))),
            Ty::ListString => Some(OutputTy::List(TyRef::from(OutputTy::Primitive(
                PrimitiveTy::String,
            )))),
            Ty::ListBool => Some(OutputTy::List(TyRef::from(OutputTy::Primitive(
                PrimitiveTy::Bool,
            )))),
            Ty::ListListInt => Some(OutputTy::List(TyRef::from(OutputTy::List(TyRef::from(
                OutputTy::Primitive(PrimitiveTy::Int),
            ))))),
            Ty::ListAny | Ty::Any => None,
        }
    }

    /// Is this a list type?
    fn is_list(self) -> bool {
        matches!(
            self,
            Ty::ListAny | Ty::ListInt | Ty::ListString | Ty::ListBool | Ty::ListListInt
        )
    }

    /// Generate a Nix literal of this type. Used by `arg_for_param`.
    #[allow(dead_code)]
    fn literal(self) -> &'static str {
        match self {
            Ty::Int => "42",
            Ty::Float => "3.14",
            Ty::Bool => "true",
            Ty::String => "\"hello\"",
            Ty::Null => "null",
            Ty::ListInt => "[ 1 2 3 ]",
            Ty::ListString => "[ \"a\" \"b\" \"c\" ]",
            Ty::ListBool => "[ true false ]",
            Ty::ListListInt => "[ [ 1 ] [ 2 ] ]",
            Ty::ListAny => "[ 1 2 3 ]",
            Ty::Any => "42",
        }
    }
}

// ==============================================================================
// Stub Function Metadata
// ==============================================================================
//
// Each composable function has a name, access paths, parameter types, and a
// result type. Functions with polymorphic parameters use `Ty::Any`.

struct StubFn {
    /// Bare function name for top-level val access (e.g. "toLower")
    bare_name: &'static str,
    /// Module-qualified paths (e.g. ["lib.strings.toLower", "lib.toLower"])
    module_paths: &'static [&'static str],
    /// Parameter types — all params before the result
    params: &'static [Ty],
    /// Result type after all params are applied
    result: Ty,
}

// Concrete functions with simple composable signatures.
// Polymorphic parameters are marked `Any` — they accept any concrete type.
const STUB_FNS: &[StubFn] = &[
    // -- Identity / trivial --
    StubFn {
        bare_name: "id",
        module_paths: &["lib.id", "lib.trivial.id"],
        params: &[Ty::Any],
        result: Ty::Any,
    },
    StubFn {
        bare_name: "boolToString",
        module_paths: &["lib.boolToString", "lib.trivial.boolToString"],
        params: &[Ty::Bool],
        result: Ty::String,
    },
    // -- String functions --
    StubFn {
        bare_name: "toLower",
        module_paths: &["lib.toLower", "lib.strings.toLower"],
        params: &[Ty::String],
        result: Ty::String,
    },
    StubFn {
        bare_name: "toUpper",
        module_paths: &["lib.toUpper", "lib.strings.toUpper"],
        params: &[Ty::String],
        result: Ty::String,
    },
    StubFn {
        bare_name: "trim",
        module_paths: &["lib.trim", "lib.strings.trim"],
        params: &[Ty::String],
        result: Ty::String,
    },
    StubFn {
        bare_name: "stringLength",
        module_paths: &["lib.stringLength", "lib.strings.stringLength"],
        params: &[Ty::String],
        result: Ty::Int,
    },
    StubFn {
        bare_name: "concatStrings",
        module_paths: &["lib.concatStrings", "lib.strings.concatStrings"],
        params: &[Ty::ListString],
        result: Ty::String,
    },
    // -- List functions --
    StubFn {
        bare_name: "head",
        module_paths: &["lib.head", "lib.lists.head"],
        params: &[Ty::ListAny],
        result: Ty::Any,
    },
    StubFn {
        bare_name: "tail",
        module_paths: &["lib.tail", "lib.lists.tail"],
        params: &[Ty::ListAny],
        result: Ty::ListAny,
    },
    StubFn {
        bare_name: "length",
        module_paths: &["lib.length", "lib.lists.length"],
        params: &[Ty::ListAny],
        result: Ty::Int,
    },
    StubFn {
        bare_name: "reverseList",
        module_paths: &["lib.reverseList", "lib.lists.reverseList"],
        params: &[Ty::ListAny],
        result: Ty::ListAny,
    },
    StubFn {
        bare_name: "singleton",
        module_paths: &["lib.singleton", "lib.lists.singleton"],
        params: &[Ty::Any],
        result: Ty::ListAny,
    },
    StubFn {
        bare_name: "range",
        module_paths: &["lib.range", "lib.lists.range"],
        params: &[Ty::Int, Ty::Int],
        result: Ty::ListInt,
    },
];

// ==============================================================================
// Access Patterns
// ==============================================================================
//
// Each generated expression uses one of these patterns to access stub functions.
// The pattern determines how the Nix code is wrapped and what context args or
// annotations are needed.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AccessPattern {
    /// Bare name access via top-level global vals: `toLower "hello"`
    Bare,
    /// Lambda parameter pattern: `{ lib, ... }: lib.strings.toLower "hello"`
    LambdaParam,
    /// pkgs.lib indirection: `{ pkgs, ... }: let lib = pkgs.lib; in lib.strings.toLower "hello"`
    PkgsLib,
}

fn arb_access_pattern() -> impl Strategy<Value = AccessPattern> {
    prop_oneof![
        Just(AccessPattern::Bare),
        Just(AccessPattern::LambdaParam),
        Just(AccessPattern::PkgsLib),
    ]
}

/// Choose a function reference string based on the access pattern.
/// For `Bare`, returns the bare name.
/// For `LambdaParam`/`PkgsLib`, picks nested "lib.strings.X" paths if available.
fn fn_ref(stub: &StubFn, pattern: AccessPattern) -> String {
    match pattern {
        AccessPattern::Bare => stub.bare_name.to_string(),
        AccessPattern::LambdaParam | AccessPattern::PkgsLib => {
            // Randomly pick between flat (lib.X) and nested (lib.strings.X) paths.
            // Prefer nested when available for better coverage.
            stub.module_paths
                .iter()
                .find(|p| p.matches('.').count() == 2)
                .or_else(|| stub.module_paths.iter().find(|p| p.matches('.').count() == 1))
                .unwrap_or(&stub.module_paths[0])
                .to_string()
        }
    }
}

// ==============================================================================
// Nix Code Generation
// ==============================================================================

/// Wrap a Nix expression in the scaffolding needed by the access pattern.
fn wrap_expr(pattern: AccessPattern, expr: &str) -> String {
    match pattern {
        AccessPattern::Bare => expr.to_string(),
        AccessPattern::LambdaParam => {
            format!("{{ lib, ... }}: {expr}")
        }
        AccessPattern::PkgsLib => {
            format!("{{ pkgs, ... }}: let lib = pkgs.lib; in {expr}")
        }
    }
}

/// Build context args for patterns that need them.
fn make_context_args(
    pattern: AccessPattern,
    registry: &TypeAliasRegistry,
) -> HashMap<SmolStr, ParsedTy> {
    match pattern {
        AccessPattern::LambdaParam => {
            let lib_ty = registry.get("Lib").expect("Lib alias must exist").clone();
            let mut map = HashMap::new();
            map.insert(SmolStr::new("lib"), lib_ty);
            map
        }
        AccessPattern::PkgsLib => {
            let pkgs_ty = registry.get("Pkgs").expect("Pkgs alias must exist").clone();
            let mut map = HashMap::new();
            map.insert(SmolStr::new("pkgs"), pkgs_ty);
            map
        }
        _ => HashMap::new(),
    }
}

/// Check a composed expression and return the inferred type of the body.
///
/// For Bare access, uses the standard `check_file_with_aliases` path (no dummy values).
/// For lambda patterns (LambdaParam, PkgsLib), extracts the body type from the lambda.
fn check_composed_expr(
    nix_src: &str,
    pattern: AccessPattern,
    registry: &TypeAliasRegistry,
) -> OutputTy {
    let context_args = make_context_args(pattern, registry);

    let root_ty = match pattern {
        AccessPattern::Bare => get_inferred_root_with_aliases(nix_src, registry),
        AccessPattern::LambdaParam | AccessPattern::PkgsLib => {
            get_inferred_root_with_aliases_and_context(nix_src, registry, context_args)
        }
    };

    match pattern {
        AccessPattern::Bare => root_ty,
        AccessPattern::LambdaParam | AccessPattern::PkgsLib => {
            // Root type is a lambda { lib, ... }: body  or  { pkgs, ... }: body.
            match root_ty {
                OutputTy::Lambda { body, .. } => (*body.0).clone(),
                other => panic!(
                    "expected lambda type for {:?} pattern, got: {}\nsrc: {}",
                    pattern, other, nix_src
                ),
            }
        }
    }
}

/// Crash-freedom check for context arg patterns.
fn check_no_crash_with_context(
    nix_src: &str,
    pattern: AccessPattern,
    registry: Option<&TypeAliasRegistry>,
) {
    if matches!(pattern, AccessPattern::LambdaParam | AccessPattern::PkgsLib) {
        if let Some(reg) = registry {
            let context_args = make_context_args(pattern, reg);
            let _ = check_str_with_aliases_and_context(nix_src, reg, context_args);
        } else {
            let _ = check_str(nix_src);
        }
    } else {
        match registry {
            Some(reg) => {
                let _ = crate::tests::check_str_with_aliases(nix_src, reg);
            }
            None => {
                let _ = check_str(nix_src);
            }
        }
    }
}

// ==============================================================================
// Strategy 1: Direct Application
// ==============================================================================
//
// Pick a concrete function and generate a matching argument. Expected output
// type is known. Randomly choose between access patterns.

/// Get the element type of a list type. Returns `Any` if not a known list type.
fn list_element(ty: Ty) -> Ty {
    match ty {
        Ty::ListInt => Ty::Int,
        Ty::ListString => Ty::String,
        Ty::ListBool => Ty::Bool,
        Ty::ListListInt => Ty::ListInt,
        Ty::ListAny => Ty::Any,
        _ => Ty::Any,
    }
}

/// Resolve the result type when a function is applied to a concrete argument.
/// For `Any`/`ListAny` result types (polymorphic), the result depends on the input.
fn resolve_result(stub: &StubFn, arg_ty: Ty) -> Ty {
    match stub.result {
        Ty::Any => {
            // Polymorphic — result type follows from the argument.
            if stub.params.len() == 1 {
                match stub.params[0] {
                    Ty::Any => arg_ty,              // id :: a -> a
                    Ty::ListAny => list_element(arg_ty), // head :: [a] -> a
                    _ => Ty::Any,
                }
            } else {
                Ty::Any
            }
        }
        Ty::ListAny => {
            // e.g. singleton :: a -> [a], tail :: [a] -> [a]
            if stub.params.len() == 1 {
                match stub.params[0] {
                    Ty::Any => {
                        // singleton :: a -> [a] — wrap arg in list
                        match arg_ty {
                            Ty::Int => Ty::ListInt,
                            Ty::String => Ty::ListString,
                            Ty::Bool => Ty::ListBool,
                            _ => Ty::ListAny,
                        }
                    }
                    Ty::ListAny => arg_ty, // tail/reverseList :: [a] -> [a]
                    _ => Ty::ListAny,
                }
            } else {
                Ty::ListAny
            }
        }
        other => other,
    }
}

/// Generate a concrete argument for a parameter type.
fn arg_for_param(param: Ty) -> (Ty, &'static str) {
    match param {
        Ty::Int => (Ty::Int, "42"),
        Ty::Float => (Ty::Float, "3.14"),
        Ty::Bool => (Ty::Bool, "true"),
        Ty::String => (Ty::String, "\"hello\""),
        Ty::Null => (Ty::Null, "null"),
        Ty::ListString => (Ty::ListString, "[ \"a\" \"b\" \"c\" ]"),
        Ty::ListInt => (Ty::ListInt, "[ 1 2 3 ]"),
        Ty::ListBool => (Ty::ListBool, "[ true false ]"),
        Ty::ListListInt => (Ty::ListListInt, "[ [ 1 ] [ 2 ] ]"),
        Ty::ListAny => (Ty::ListInt, "[ 1 2 3 ]"),
        Ty::Any => (Ty::Int, "42"),
    }
}

/// Strategy: pick a random stub function, access pattern, and generate a direct
/// application expression with all arguments supplied.
fn arb_stub_direct_apply() -> impl Strategy<Value = (AccessPattern, String, Ty)> {
    let stub_idx = 0..STUB_FNS.len();
    (stub_idx, arb_access_pattern()).prop_map(|(idx, pattern)| {
        let stub = &STUB_FNS[idx];
        let func_ref = fn_ref(stub, pattern);

        // Build the full application by supplying all parameters
        let mut expr = func_ref;
        let mut last_arg_ty = Ty::Any;
        for &param in stub.params {
            let (arg_ty, arg_str) = arg_for_param(param);
            last_arg_ty = arg_ty;
            write!(expr, " ({arg_str})").unwrap();
        }

        let result_ty = resolve_result(stub, last_arg_ty);
        let nix_src = wrap_expr(pattern, &expr);
        (pattern, nix_src, result_ty)
    })
}

// ==============================================================================
// Strategy 2: Pipeline Composition
// ==============================================================================
//
// Chain 2-3 functions where output types match input types. Can mix access
// patterns within a single expression (always wrapping with the outermost one).

/// Functions that can participate in pipeline chains, grouped by their
/// (input, output) type signature for the first parameter.
struct PipelineFn {
    bare_name: &'static str,
    module_path: &'static str,
    /// Extra arguments to supply before the "piped" argument
    extra_args: &'static str,
    input: Ty,
    output: Ty,
    /// Whether this function is available as a top-level global val
    has_global_val: bool,
}

const PIPELINE_FNS: &[PipelineFn] = &[
    // string -> string
    PipelineFn { bare_name: "toLower", module_path: "lib.strings.toLower", extra_args: "", input: Ty::String, output: Ty::String, has_global_val: true },
    PipelineFn { bare_name: "toUpper", module_path: "lib.strings.toUpper", extra_args: "", input: Ty::String, output: Ty::String, has_global_val: true },
    PipelineFn { bare_name: "trim", module_path: "lib.strings.trim", extra_args: "", input: Ty::String, output: Ty::String, has_global_val: true },
    // string -> int
    PipelineFn { bare_name: "stringLength", module_path: "lib.strings.stringLength", extra_args: "", input: Ty::String, output: Ty::Int, has_global_val: true },
    // string -> bool (only in module, not a top-level val)
    PipelineFn { bare_name: "hasPrefix", module_path: "lib.strings.hasPrefix", extra_args: "\"x\"", input: Ty::String, output: Ty::Bool, has_global_val: false },
    // string -> [string] (only in module)
    PipelineFn { bare_name: "splitString", module_path: "lib.strings.splitString", extra_args: "\",\"", input: Ty::String, output: Ty::ListString, has_global_val: false },
    PipelineFn { bare_name: "stringToCharacters", module_path: "lib.strings.stringToCharacters", extra_args: "", input: Ty::String, output: Ty::ListString, has_global_val: false },
    // bool -> string
    PipelineFn { bare_name: "boolToString", module_path: "lib.boolToString", extra_args: "", input: Ty::Bool, output: Ty::String, has_global_val: true },
    // [string] -> string
    PipelineFn { bare_name: "concatStrings", module_path: "lib.strings.concatStrings", extra_args: "", input: Ty::ListString, output: Ty::String, has_global_val: true },
    PipelineFn { bare_name: "concatStringsSep", module_path: "lib.strings.concatStringsSep", extra_args: "\",\"", input: Ty::ListString, output: Ty::String, has_global_val: false },
    // [a] -> int
    PipelineFn { bare_name: "length", module_path: "lib.lists.length", extra_args: "", input: Ty::ListAny, output: Ty::Int, has_global_val: true },
];

/// Check if a type can be passed where `expected` is required.
/// `ListAny` accepts any list type.
fn type_matches(actual: Ty, expected: Ty) -> bool {
    if actual == expected {
        return true;
    }
    // ListAny matches any list type
    if expected == Ty::ListAny && actual.is_list() {
        return true;
    }
    if actual == Ty::ListAny && expected.is_list() {
        return true;
    }
    false
}

/// Find pipeline functions whose input matches the given type.
/// For Bare access, only return functions that have top-level global vals.
fn compatible_successors(current_ty: Ty, pattern: AccessPattern) -> Vec<usize> {
    PIPELINE_FNS
        .iter()
        .enumerate()
        .filter(|(_, f)| {
            type_matches(current_ty, f.input)
                && (pattern != AccessPattern::Bare || f.has_global_val)
        })
        .map(|(i, _)| i)
        .collect()
}

/// Build a pipeline function reference string based on access pattern.
fn pipeline_fn_ref(pf: &PipelineFn, pattern: AccessPattern) -> String {
    match pattern {
        AccessPattern::Bare => pf.bare_name.to_string(),
        _ => pf.module_path.to_string(),
    }
}

/// Strategy: generate a chain of 2-3 compatible pipeline functions.
fn arb_stub_pipeline() -> impl Strategy<Value = (AccessPattern, String, Ty)> {
    let chain_len = 2..=3usize;
    (arb_access_pattern(), chain_len).prop_flat_map(|(pattern, len)| {
        // Pick `len` random indices; we'll use them to select from compatible candidates.
        let step_selectors = proptest::collection::vec(any::<prop::sample::Index>(), len);
        (Just(pattern), step_selectors).prop_filter_map(
            "no compatible pipeline found",
            move |(pattern, selectors)| {
                let mut current_ty = Ty::String;
                let mut inner_expr = String::from("\"hello\"");

                for selector in &selectors {
                    let candidates = compatible_successors(current_ty, pattern);
                    if candidates.is_empty() {
                        return None;
                    }
                    let fn_idx = candidates[selector.index(candidates.len())];
                    let pf = &PIPELINE_FNS[fn_idx];
                    let fref = pipeline_fn_ref(pf, pattern);

                    if pf.extra_args.is_empty() {
                        inner_expr = format!("({fref} ({inner_expr}))");
                    } else {
                        inner_expr = format!("({fref} {} ({inner_expr}))", pf.extra_args);
                    }
                    current_ty = pf.output;
                }

                let nix_src = wrap_expr(pattern, &inner_expr);
                Some((pattern, nix_src, current_ty))
            },
        )
    })
}

// ==============================================================================
// Strategy 3: Higher-Order Function Application
// ==============================================================================
//
// Apply a higher-order list function (map, filter, all, any, count) to a
// compatible function and list argument.

struct HofCase {
    /// HOF access path (e.g. "lib.lists.map")
    module_path: &'static str,
    /// The function argument as a bare name (for global val or inline lambda).
    /// Inline lambdas (starting with '(') don't need qualification.
    /// Kept for documentation — currently only qualified form is used since
    /// HOF patterns always go through module access.
    #[allow(dead_code)]
    fn_arg_bare: &'static str,
    /// The function argument as a module-qualified name (for let-annotated/lambda patterns).
    /// Same as bare for inline lambdas.
    fn_arg_qualified: &'static str,
    /// The list argument
    list_arg: &'static str,
    /// Expected result type
    result: Ty,
}

const HOF_CASES: &[HofCase] = &[
    // map boolToString [true false] -> [string]
    HofCase {
        module_path: "lib.lists.map",
        fn_arg_bare: "boolToString",
        fn_arg_qualified: "lib.boolToString",
        list_arg: "[ true false ]",
        result: Ty::ListString,
    },
    // map toLower ["A" "B"] -> [string]
    HofCase {
        module_path: "lib.lists.map",
        fn_arg_bare: "toLower",
        fn_arg_qualified: "lib.toLower",
        list_arg: "[ \"A\" \"B\" ]",
        result: Ty::ListString,
    },
    // map toUpper ["a" "b"] -> [string]
    HofCase {
        module_path: "lib.lists.map",
        fn_arg_bare: "toUpper",
        fn_arg_qualified: "lib.toUpper",
        list_arg: "[ \"a\" \"b\" ]",
        result: Ty::ListString,
    },
    // map stringLength ["abc" "de"] -> [int]
    HofCase {
        module_path: "lib.lists.map",
        fn_arg_bare: "stringLength",
        fn_arg_qualified: "lib.stringLength",
        list_arg: "[ \"abc\" \"de\" ]",
        result: Ty::ListInt,
    },
    // filter (x: true) [1 2 3] -> [int]
    HofCase {
        module_path: "lib.lists.filter",
        fn_arg_bare: "(x: true)",
        fn_arg_qualified: "(x: true)",
        list_arg: "[ 1 2 3 ]",
        result: Ty::ListInt,
    },
    // all (x: true) [1 2] -> bool
    HofCase {
        module_path: "lib.lists.all",
        fn_arg_bare: "(x: true)",
        fn_arg_qualified: "(x: true)",
        list_arg: "[ 1 2 ]",
        result: Ty::Bool,
    },
    // any (x: true) [1 2] -> bool
    HofCase {
        module_path: "lib.lists.any",
        fn_arg_bare: "(x: true)",
        fn_arg_qualified: "(x: true)",
        list_arg: "[ 1 2 ]",
        result: Ty::Bool,
    },
    // count (x: true) [1 2] -> int
    HofCase {
        module_path: "lib.lists.count",
        fn_arg_bare: "(x: true)",
        fn_arg_qualified: "(x: true)",
        list_arg: "[ 1 2 ]",
        result: Ty::Int,
    },
    // concatMap singleton [1 2] -> [int]
    HofCase {
        module_path: "lib.lists.concatMap",
        fn_arg_bare: "singleton",
        fn_arg_qualified: "lib.singleton",
        list_arg: "[ 1 2 ]",
        result: Ty::ListInt,
    },
    // map singleton [1 2] -> [[int]]
    HofCase {
        module_path: "lib.lists.map",
        fn_arg_bare: "singleton",
        fn_arg_qualified: "lib.singleton",
        list_arg: "[ 1 2 ]",
        result: Ty::ListListInt,
    },
];

/// Strategy: pick a random HOF case and access pattern.
/// The HOF is always accessed via module path (it needs `lib.lists.X`);
/// the fn_arg uses bare name for global val patterns and qualified for module patterns.
fn arb_stub_hof() -> impl Strategy<Value = (AccessPattern, String, Ty)> {
    let case_idx = 0..HOF_CASES.len();
    // HOF requires module access, so we only use patterns that provide `lib`.
    let pattern = prop_oneof![
        Just(AccessPattern::LambdaParam),
        Just(AccessPattern::PkgsLib),
    ];
    (case_idx, pattern).prop_map(|(idx, pattern)| {
        let case = &HOF_CASES[idx];
        // In let-annotated/lambda patterns, bare names aren't global vals —
        // use module-qualified fn_arg instead.
        let fn_arg = case.fn_arg_qualified;
        let expr = format!("{} {} {}", case.module_path, fn_arg, case.list_arg);
        let nix_src = wrap_expr(pattern, &expr);
        (pattern, nix_src, case.result)
    })
}

// ==============================================================================
// Strategy 4: Deep Random Composition (Crash-Freedom Only)
// ==============================================================================
//
// Pick 2-5 random stub functions and compose them in arbitrary nesting.
// No type tracking — just verify no panic.

fn arb_stub_compose_deep() -> impl Strategy<Value = (AccessPattern, String)> {
    (
        arb_access_pattern(),
        proptest::collection::vec(0..STUB_FNS.len(), 2..=5),
    )
        .prop_map(|(pattern, fn_indices)| {
            // Build a nested expression: f1(f2(f3(...)))
            // Start from a literal and wrap outward.
            let mut expr = String::from("42");

            for &idx in fn_indices.iter() {
                let stub = &STUB_FNS[idx];
                let fref = fn_ref(stub, pattern);

                // Supply extra args for multi-param functions, then our accumulated expr
                if stub.params.len() > 1 {
                    let mut call = format!("({fref}");
                    // Supply dummy literals for all params except the last
                    for &param in &stub.params[..stub.params.len() - 1] {
                        let (_, lit) = arg_for_param(param);
                        write!(call, " ({lit})").unwrap();
                    }
                    write!(call, " ({expr}))").unwrap();
                    expr = call;
                } else {
                    expr = format!("({fref} ({expr}))");
                }
            }

            let nix_src = wrap_expr(pattern, &expr);
            (pattern, nix_src)
        })
}

// ==============================================================================
// Property Tests
// ==============================================================================
//
proptest! {
    #![proptest_config(ProptestConfig {
        cases: 512,
        .. ProptestConfig::default()
    })]

    // -------------------------------------------------------------------------
    // Direct application with stubs — verify exact types
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_direct_apply_with_stubs(
        (pattern, nix_src, expected_ty) in arb_stub_direct_apply()
    ) {
        let registry = &*COMPOSABLE_REGISTRY;
        let inferred = check_composed_expr(&nix_src, pattern, &registry);

        // For concrete result types, assert exact match.
        // For `Any` (polymorphic), the result is some concrete type — just check it's valid.
        if let Some(expected) = expected_ty.to_output_ty() {
            prop_assert_eq!(
                inferred, expected,
                "pattern={:?}\nsrc:\n{}", pattern, nix_src
            );
        }
    }

    // -------------------------------------------------------------------------
    // Direct application without stubs — crash-freedom
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_direct_apply_no_stubs(
        (_pattern, nix_src, _expected_ty) in arb_stub_direct_apply()
    ) {
        // Without stubs, function names are unresolved free vars.
        // We only care that inference doesn't panic.
        let _ = check_str(&nix_src);
    }

    // -------------------------------------------------------------------------
    // Pipeline composition with stubs — verify exact types
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_pipeline_with_stubs(
        (pattern, nix_src, expected_ty) in arb_stub_pipeline()
    ) {
        let registry = &*COMPOSABLE_REGISTRY;
        let inferred = check_composed_expr(&nix_src, pattern, &registry);

        if let Some(expected) = expected_ty.to_output_ty() {
            prop_assert_eq!(
                inferred, expected,
                "pattern={:?}\nsrc:\n{}", pattern, nix_src
            );
        }
    }

    // -------------------------------------------------------------------------
    // Pipeline composition without stubs — crash-freedom
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_pipeline_no_stubs(
        (_pattern, nix_src, _expected_ty) in arb_stub_pipeline()
    ) {
        let _ = check_str(&nix_src);
    }

    // -------------------------------------------------------------------------
    // HOF composition with stubs — verify exact types
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_hof_with_stubs(
        (pattern, nix_src, expected_ty) in arb_stub_hof()
    ) {
        let registry = &*COMPOSABLE_REGISTRY;
        let inferred = check_composed_expr(&nix_src, pattern, &registry);

        if let Some(expected) = expected_ty.to_output_ty() {
            prop_assert_eq!(
                inferred, expected,
                "pattern={:?}\nsrc:\n{}", pattern, nix_src
            );
        }
    }

    // -------------------------------------------------------------------------
    // HOF composition without stubs — crash-freedom
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_hof_no_stubs(
        (_pattern, nix_src, _expected_ty) in arb_stub_hof()
    ) {
        let _ = check_str(&nix_src);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    // -------------------------------------------------------------------------
    // Deep composition with stubs — crash-freedom
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_compose_deep_with_stubs(
        (pattern, nix_src) in arb_stub_compose_deep()
    ) {
        let registry = &*COMPOSABLE_REGISTRY;
        check_no_crash_with_context(&nix_src, pattern, Some(registry));
    }

    // -------------------------------------------------------------------------
    // Deep composition without stubs — crash-freedom
    // -------------------------------------------------------------------------
    #[test]
    fn test_stub_compose_deep_no_stubs(
        (_pattern, nix_src) in arb_stub_compose_deep()
    ) {
        let _ = check_str(&nix_src);
    }
}
