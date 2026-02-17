use indoc::indoc;
use lang_ast::{module, tests::TestDatabase, Module};
use lang_ty::{arc_ty, OutputTy, PrimitiveTy};

use crate::aliases::TypeAliasRegistry;
use crate::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use crate::{check_file_with_aliases, InferenceResult};

use super::check_file;

pub fn check_str(src: &str) -> (Module, Result<InferenceResult, TixDiagnostic>) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = module(&db, file);
    (module, check_file(&db, file))
}

pub fn check_str_with_aliases(
    src: &str,
    aliases: &TypeAliasRegistry,
) -> (Module, Result<InferenceResult, TixDiagnostic>) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = module(&db, file);
    (module, check_file_with_aliases(&db, file, aliases))
}

pub fn get_inferred_root_with_aliases(src: &str, aliases: &TypeAliasRegistry) -> OutputTy {
    let (module, inference) = check_str_with_aliases(src, aliases);
    let inference = inference.expect("No type error");
    inference
        .expr_ty_map
        .get(module.entry_expr)
        .expect("No type for root module entry")
        .clone()
}

pub fn get_inferred_root(src: &str) -> OutputTy {
    let (module, inference) = check_str(src);

    let inference = inference.expect("No type error");

    inference
        .expr_ty_map
        .get(module.entry_expr)
        .expect("No type for root module entry")
        .clone()
}

pub fn get_check_error(src: &str) -> TixDiagnosticKind {
    let (_, inference) = check_str(src);

    inference.expect_err("Expected an inference error").kind
}

/// Get the diagnostic message string for a failing Nix expression.
pub fn get_diagnostic_message(src: &str) -> String {
    get_check_error(src).to_string()
}

#[track_caller]
pub fn expect_ty_inference(src: &str, expected: OutputTy) {
    let root_ty = get_inferred_root(src);

    assert_eq!(root_ty, expected)
}

#[track_caller]
pub fn expect_diagnostic_kind(src: &str, expected: TixDiagnosticKind) {
    let error = get_check_error(src);

    assert_eq!(error, expected)
}

macro_rules! test_case {
    ($name:ident, $file:tt, $ty:tt) => {
        #[test]
        fn $name() {
            let file = indoc! { $file };
            let ty = arc_ty!($ty);
            expect_ty_inference(file, ty);
        }
    };
}

fn registry_from_tix(tix_src: &str) -> TypeAliasRegistry {
    let file = comment_parser::parse_tix_file(tix_src).expect("parse tix");
    let mut registry = TypeAliasRegistry::new();
    registry.load_tix_file(&file);
    registry
}

macro_rules! alias_test_case {
    ($name:ident, tix: $tix:expr, nix: $nix:tt, $ty:tt) => {
        #[test]
        fn $name() {
            let registry = registry_from_tix($tix);
            let nix_src = indoc! { $nix };
            let ty = get_inferred_root_with_aliases(nix_src, &registry);
            let expected = arc_ty!($ty);
            assert_eq!(ty, expected);
        }
    };
}

macro_rules! error_case {
    ($name:ident, $file:tt, matches $pat:pat) => {
        #[test]
        fn $name() {
            let file = indoc! { $file };
            let error = get_check_error(file);
            assert!(
                matches!(error, $pat),
                "expected {}, got: {error:?}",
                stringify!($pat)
            );
        }
    };
    ($name:ident, $file:tt, $expected:expr) => {
        #[test]
        fn $name() {
            let file = indoc! { $file };
            expect_diagnostic_kind(file, $expected);
        }
    };
}

/// Test that a diagnostic message contains / does not contain a substring.
macro_rules! diagnostic_msg {
    ($name:ident, $file:expr, contains $needle:expr) => {
        #[test]
        fn $name() {
            let msg = get_diagnostic_message($file);
            assert!(
                msg.contains($needle),
                "expected message to contain {:?}, got: {msg:?}",
                $needle,
            );
        }
    };
    ($name:ident, $file:expr, not contains $needle:expr) => {
        #[test]
        fn $name() {
            let msg = get_diagnostic_message($file);
            assert!(
                !msg.contains($needle),
                "expected message NOT to contain {:?}, got: {msg:?}",
                $needle,
            );
        }
    };
}

test_case!(
    simple_types,
    "{
        num = 1;
        str = \"foo\";
        bool = true;
        null = null;
        float = 3.14;
        # add remains polymorphic with unresolved overload — variables for a, b, result
        add = a: b: a + b;
        lst = [(1) (2)];
    }
    ",
    {
    "num": (Int),
    "str": (String),
    "bool": (Bool),
    "null": (Null),
    "float": (Float),
    "add": ((# 0) -> (# 1) -> (# 2)),
    "lst": [Int]
    }
);

test_case!(equality, "1 == 0", Bool);

test_case!(basic_merge,
    "
        {
            a = 1;
            b = 2;
        }
        // {
            a = \"hi\";
            c = ./merge.nix;
        }
    ", {
    "a": (String),
    "b": (Int),
    "c": (Path)
});

test_case!(
    simple_func,
    "
    (a: b: a + b) 1 2
    ",
    Int
);

test_case!(
    simple_let_gen,
    "
    let
        id = (a: a);
    in
        id 1
    ",
    Int
);

test_case!(
    simple_let_gen_overload,
    "
    let
        add = a: b: a + b;
    in
        {
            int = add 1 2;
            float = add 3.14 2;
            str = add \"hi\" ./test.nix;
        }
    ",
    {
        "int": (Int),
        "float": (Float),
        "str": (String)
    }
);

test_case!(
    mutual_def,
    "
    let
    even =
        x:
            if x == 0 then
                true
            else if x == 1 then
                false
            else
                odd (x - 1);
    odd =
        x:
            if x == 0 then
                false
            else if x == 1 then
                true
            else
                even (x - 1);
    in
    odd 17
    ",
    Bool
);

test_case!(
    overloads,
    "
    {
        neg_int = -(1 * 5);
        neg_float = -(3.14);

        int_float_add = 1 + 3.14;
        float_int_add = 3.14 + 1;
        int_add = 1 + 3;
        float_add = 3.14 + 5.3;

        int_mul = 4 * 5;
        float_int_mul = 3.14 * 5;

        int_div = 4 / 3;
        float_int_div = 5.0 / 2;

        string_add = \"hello\" + ''world'';
        path_add = ./overload.nix + ./overload.nix;
        string_path_add = ''hello'' + ./overload.nix;
        path_string_add = ./overload.nix + ''hello'';
    }
    ",
    {
        "neg_int": Int,
        "neg_float": Float,

        "int_float_add": Float,
        "float_int_add": Float,
        "int_add": Int,
        "float_add": Float,

        "int_mul": Int,
        "float_int_mul": Float,

        "int_div": Int,
        "float_int_div": Float,

        "string_add": String,
        "path_add": Path,
        "string_path_add": String,
        "path_string_add": Path,
    }
);

// With subtyping, row polymorphism is replaced by width subtyping.
// An open attrset pattern (`{ ..., ... }`) means the function accepts
// records with at least the specified fields.
test_case!(
    row_poly,
    "
        arg: (arg.foo == 10) && (arg.bar == ./test.nix)
    ",
    (({
        "bar": (Path),
        "foo": (Int)
        ; ...
    }) -> Bool)
);

test_case!(
    rec_fun,
    "
    let
        fib =
            n:
            if n == 0 then
            0
            else if n == 1 then
            1
            else
            fib (n - 1) + fib (n - 2);

    in
        fib 3
    ",
    Int
);

test_case!(
    inherit_from,
    "
    let
        simple = {
            foo = 100;
            bar = ''123'';
        };
    in {
        inherit (simple) foo bar;
        a = ''test123'';
    }
    ",
    {
        "foo": Int,
        "bar": String,
        "a": String
    }
);

test_case!(
    select,
    "
    let
        simple = {
            foo = 100;
        };
    in
        simple.foo
    ",
    Int
);

test_case!(
    complicated_row_poly_overload,
    "
    let
        func = { other, ... }@arg: (arg.quz + (arg.foo + arg.bar) + (arg.bar + arg.baz));
    in

    func {
        quz = 0;
        foo = 1;
        bar = 3.14;
        baz = 5;
        other = ''hello'';
    }
    ",
    Float
);

test_case!(
    simple_ty_annotation,
    "
    let
            /**
                type: foo :: string
            */
            foo = ''hi'';
        in
        foo
    ",
    String
);

// With subtyping, this is a type mismatch between string and int.
error_case!(
    type_annotation_mis_match,
    "
        let
            /**
                type: foo :: string
            */
            foo = 1;
        in
        foo
    ",
    TixDiagnosticKind::TypeMismatch {
        actual: OutputTy::Primitive(PrimitiveTy::Int),
        expected: OutputTy::Primitive(PrimitiveTy::String),
    }
);

// ==============================================================================
// Pattern field doc comment annotations
// ==============================================================================

test_case!(
    pat_field_annotation,
    "
    let
        f = {
            /** type: x :: int */
            x,
            /** type: y :: string */
            y
        }: { inherit x y; };
    in
    f { x = 1; y = \"hello\"; }
    ",
    { "x": (Int), "y": (String) }
);

test_case!(
    pat_field_annotation_constrains_body,
    "
    let
        f = {
            /** type: x :: int */
            x
        }: x + 1;
    in
    f { x = 42; }
    ",
    Int
);

// The annotation constrains x to string inside the body, so using it
// in a numeric context (multiplication) produces a type mismatch.
error_case!(
    pat_field_annotation_mismatch,
    "
        let
            f = {
                /** type: x :: string */
                x
            }: x * 2;
        in
        f { x = \"hello\"; }
    ",
    matches TixDiagnosticKind::TypeMismatch { .. }
);

test_case!(
    pat_field_annotation_with_default,
    "
    let
        f = {
            /** type: x :: int */
            x ? 0
        }: x;
    in
    f { x = 42; }
    ",
    Int
);

test_case!(
    pat_field_annotation_top_level_lambda_called,
    "
    let
        f = {
            /** type: name :: string */
            name,
            /** type: age :: int */
            age
        }:
        { inherit name age; };
    in
    f { name = ''alice''; age = 30; }
    ",
    { "name": (String), "age": (Int) }
);

// The previous tests wrap lambdas in let-bindings; annotations there work
// because the let binding goes through SCC group inference. These tests verify
// that annotations also work on the root-level lambda (the pattern in lsp-dev.nix).
test_case!(
    pat_field_annotation_root_lambda,
    "
    {
        /** type: x :: int */
        x,
        /** type: y :: string */
        y
    }: { inherit x y; }
    ",
    ({ "x": (Int), "y": (String) } -> { "x": (Int), "y": (String) })
);

#[test]
fn pat_field_annotation_root_lambda_constrains_body() {
    // The annotation constrains x to int inside the body, so x + 1
    // should infer as int (not a polymorphic variable).
    let file = indoc! { "
        {
            /** type: x :: int */
            x
        }: x + 1
    " };

    let root_ty = get_inferred_root(file);
    let expected = arc_ty!({ "x": (Int) } -> Int);
    assert_eq!(
        root_ty, expected,
        "annotated root lambda body should be int"
    );
}

// The annotation constrains x to string, but the body uses it as a number.
error_case!(
    pat_field_annotation_root_lambda_mismatch,
    "
        {
            /** type: x :: string */
            x
        }: x * 2
    ",
    matches TixDiagnosticKind::TypeMismatch { .. }
);

/// Look up the type of a named binding by text name, with aliases loaded.
/// When the same name has multiple NameIds (e.g. definition + inherit reference),
/// prefer the version without unions/intersections (the clean early-canonicalized form).
fn get_name_type_with_aliases(src: &str, name: &str, aliases: &TypeAliasRegistry) -> OutputTy {
    let (module, inference) = check_str_with_aliases(src, aliases);
    let inference = inference.expect("No type error");

    let mut best: Option<OutputTy> = None;
    for (name_id, name_data) in module.names() {
        if name_data.text == name {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                let is_better = match &best {
                    None => true,
                    Some(prev) => {
                        !ty.contains_union_or_intersection()
                            && prev.contains_union_or_intersection()
                    }
                };
                if is_better {
                    best = Some(ty.clone());
                }
            }
        }
    }
    best.unwrap_or_else(|| panic!("Name '{name}' not found in module"))
}

fn get_name_type(src: &str, name: &str) -> OutputTy {
    get_name_type_with_aliases(src, name, &TypeAliasRegistry::default())
}

/// Early canonicalization captures the polymorphic type of `apply` before
/// use-site extrusions add concrete bounds (`int`, `string`) from call sites
/// like `apply add 2` or `apply (x: x + "hi") "foo"`.
#[test]
fn apply_polymorphism() {
    let file = indoc! { "
        let
            apply = fn: args: fn args;
            add = a: b: a + b;
            addTwo = apply add 2;
            strApply = apply (x: x + \"hi\") \"foo\";
        in
        {
            inherit apply addTwo strApply;
        }
    " };

    // `apply` should have the clean polymorphic type (a -> b) -> a -> b,
    // not contaminated by concrete bounds from use sites.
    let apply_ty = get_name_type(file, "apply");
    assert!(
        !apply_ty.contains_union_or_intersection(),
        "apply should be purely polymorphic, got: {apply_ty}"
    );
    // Normalized: (a -> b) -> a -> b, i.e. Lambda { param: Lambda(0 -> 1), body: Lambda(0 -> 1) }
    let expected = arc_ty!(((# 0) -> (# 1)) -> (# 0) -> (# 1));
    assert_eq!(apply_ty, expected, "apply should be (a -> b) -> a -> b");

    // `addTwo` should now infer as `number -> number` — the partial application
    // of `add` to an int constrains the remaining operand and result via Number.
    let add_two_ty = get_name_type(file, "addTwo");
    assert_eq!(add_two_ty, arc_ty!(Number -> Number));

    // `strApply` should infer as `String` — the extrusion of `apply` gets
    // independent fresh vars, so `addTwo`'s Number constraints don't leak here.
    let str_apply_ty = get_name_type(file, "strApply");
    assert_eq!(str_apply_ty, arc_ty!(String));
}

// PBT assertion builtins: applying `__pbt_assert_int` to a lambda param
// constrains it to `int` via application contravariance. The param gets
// `int` as an upper bound (negative position), while the body is independent.
test_case!(
    pbt_assert_builtin_constrains_param,
    "(p: let __c = __pbt_assert_int p; in 42)",
    (Int -> Int)
);

// The assertion builtin itself has type `prim -> prim`.
test_case!(
    pbt_assert_builtin_type,
    "__pbt_assert_int",
    (Int -> Int)
);

// ==============================================================================
// Nix builtin type inference
// ==============================================================================

// Global builtins (available without `builtins.` prefix).
test_case!(builtin_tostring, "toString 42", String);
test_case!(builtin_isnull, "isNull null", Bool);
// `throw` returns a fresh type variable — the return type is unconstrained.
test_case!(builtin_throw, "throw \"err\"", (# 0));

// Builtins accessed via the `builtins` attrset.
test_case!(builtin_head, "builtins.head [1 2 3]", Int);
test_case!(builtin_length, "builtins.length [1 2]", Int);
test_case!(builtin_map, "builtins.map (x: x + 1) [1 2]", [Int]);
test_case!(builtin_filter, "builtins.filter (x: x == 1) [1 2]", [Int]);
test_case!(builtin_tail, "builtins.tail [''a'' ''b'']", [String]);
test_case!(
    builtin_attr_names,
    "builtins.attrNames { a = 1; }",
    [String]
);

// Polymorphism through let — each use of `h` gets independent type vars.
test_case!(
    builtin_polymorphic_let,
    "let h = builtins.head; in { a = h [1]; b = h [''x'']; }",
    { "a": Int, "b": String }
);

// ==============================================================================
// Number-based partial resolution for arithmetic ops
// ==============================================================================

// Binary subtraction: both operands and result are immediately constrained to Number.
test_case!(
    sub_lambda_number,
    "a: b: a - b",
    (Number -> Number -> Number)
);

// Multiplication: same as subtraction.
test_case!(
    mul_lambda_number,
    "a: b: a * b",
    (Number -> Number -> Number)
);

// Division: same.
test_case!(
    div_lambda_number,
    "a: b: a / b",
    (Number -> Number -> Number)
);

// Unary negation constrains the operand to Number immediately.
test_case!(negate_lambda_number, "a: -a", (Number -> Number));

// Fully-applied arithmetic still produces precise types.
test_case!(sub_concrete_int, "3 - 1", Int);
test_case!(mul_concrete_float, "3.14 * 2", Float);

// Partial application of + with int: the unknown side gets Number.
test_case!(
    add_partial_number,
    "let add = a: b: a + b; in add 1",
    (Number -> Number)
);

// Partial application of + with string lhs: the result is pinned to string.
test_case!(
    add_partial_string,
    "let add = a: b: a + b; in add ''hello''",
    ((# 0) -> String)
);

// Partial application of + with path lhs: the result is pinned to path.
test_case!(
    add_partial_path,
    "let add = a: b: a + b; in add ./test.nix",
    ((# 0) -> Path)
);

// Type error: can't negate a string.
error_case!(
    negate_string_error,
    r#"-"hello""#,
    TixDiagnosticKind::TypeMismatch {
        actual: OutputTy::Primitive(PrimitiveTy::String),
        expected: OutputTy::Primitive(PrimitiveTy::Number),
    }
);

// Type error: can't subtract with a string.
error_case!(
    sub_string_error,
    r#""hello" - 1"#,
    TixDiagnosticKind::TypeMismatch {
        actual: OutputTy::Primitive(PrimitiveTy::String),
        expected: OutputTy::Primitive(PrimitiveTy::Number),
    }
);

// ==============================================================================
// String / Path interpolation
// ==============================================================================

test_case!(
    interpolation_simple,
    "let name = \"world\"; in \"hello ${name}\"",
    String
);

// Sub-expressions are inferred independently; the overall expression is always string.
test_case!(interpolation_non_string_expr, "\"count: ${1 + 2}\"", String);

test_case!(
    interpolation_nested,
    "let c = \"!\"; in \"a ${\"b ${c}\"}\"",
    String
);

test_case!(
    interpolation_let_binding,
    "let x = 42; in \"value: ${toString x}\"",
    String
);

test_case!(
    interpolation_multiline,
    "let name = \"world\"; in ''hello ${name}''",
    String
);

// ==============================================================================
// `with` expression
// ==============================================================================

test_case!(with_simple, "with { x = 1; }; x", Int);

test_case!(
    with_let_binding,
    "let s = { x = \"hi\"; }; in with s; x",
    String
);

test_case!(with_function, "with { f = x: x + 1; }; f 5", Int);

// Nested `with` where both envs are the same: variables resolve through the innermost.
test_case!(
    with_nested_same_env,
    "let e = { x = 1; y = \"hi\"; }; in with e; with e; { a = x; b = y; }",
    { "a": Int, "b": String }
);

// Nested `with` with disjoint envs: only the innermost is constrained,
// so names from the outer `with` that aren't in the inner one produce errors.
// TODO: multi-`with` fallthrough would resolve `x` from the outer env.
error_case!(
    with_nested_disjoint_errors,
    r#"with { x = 1; }; with { y = "hi"; }; { a = x; b = y; }"#,
    matches TixDiagnosticKind::MissingField { .. }
);

// ==============================================================================
// Recursive / self-referential types
// ==============================================================================

// Self-recursive function — tests cycle detection in canonicalization and extrude.
// `f` calls itself, so its type is recursive. The key constraint is that this
// doesn't diverge during inference or canonicalization.
#[test]
fn recursive_function() {
    let ty = get_inferred_root("let f = x: f x; in f");
    // f :: a -> b where f is applied recursively. The exact shape depends on
    // how the cycle is broken, but it must be a lambda.
    assert!(
        matches!(&ty, lang_ty::OutputTy::Lambda { .. }),
        "recursive function should produce a lambda type, got: {ty}"
    );
}

// Mutually recursive functions — tests SCC grouping and mutual type flow.
#[test]
fn mutual_recursion_types() {
    let ty = get_inferred_root("let f = x: g x; g = x: f x; in { inherit f g; }");
    // Both f and g are in the same SCC group and are mutually recursive lambdas.
    match &ty {
        lang_ty::OutputTy::AttrSet(attr) => {
            assert!(attr.fields.contains_key("f"), "should have field f");
            assert!(attr.fields.contains_key("g"), "should have field g");
        }
        _ => panic!("expected attrset, got: {ty}"),
    }
}

// ==============================================================================
// List edge cases
// ==============================================================================

// Empty list — the element type is unconstrained, producing a list of a free var.
test_case!(empty_list, "[]", [(# 0)]);

// Nested list — list of lists of ints.
test_case!(nested_list, "[[1 2] [3 4]]", [[Int]]);

// Heterogeneous list — elements of different types produce a union element type.
#[test]
fn heterogeneous_list() {
    let ty = get_inferred_root("[1 \"hi\" true]");
    match &ty {
        lang_ty::OutputTy::List(elem) => {
            assert!(
                matches!(&*elem.0, lang_ty::OutputTy::Union(_)),
                "heterogeneous list should have union element type, got: {}",
                elem.0
            );
        }
        _ => panic!("expected list type, got: {ty}"),
    }
}

// List of functions — all elements are lambdas with `+ int_literal`. The `+`
// overload partially resolves: the int operand constrains the other side to
// Number (not pinned to Int since `+` is deferred). Both param and result
// canonicalize to Number.
test_case!(
    list_of_functions,
    "[(x: x + 1) (x: x + 2)]",
    [Number -> Number]
);

// ==============================================================================
// `with` scoping — shadowing rules
// ==============================================================================

// Local let binding should shadow the `with` environment.
test_case!(
    let_shadows_with,
    "let x = 1; in with { x = \"hi\"; }; x",
    Int
);

// Lambda parameter should shadow the `with` environment.
test_case!(
    lambda_param_shadows_with,
    "(x: with { x = \"hi\"; }; x) 1",
    Int
);

// ==============================================================================
// Select edge cases
// ==============================================================================

// Select with a default expression — the result is the union of the field type
// and the default type, since either branch is possible at runtime.
#[test]
fn select_default() {
    let ty = get_inferred_root("let s = { x = 1; }; in s.x or \"fallback\"");
    // Should be union of Int and String (field exists with Int, default is String).
    match &ty {
        lang_ty::OutputTy::Union(members) => {
            assert_eq!(members.len(), 2, "expected 2 union members, got: {ty}");
        }
        // If the checker is smart enough to see that x definitely exists, it could
        // return just Int. Either is acceptable.
        lang_ty::OutputTy::Primitive(lang_ty::PrimitiveTy::Int) => {}
        _ => panic!("expected union or int, got: {ty}"),
    }
}

// Chained select — accessing a nested attrset.
test_case!(chained_select, "let s = { a = { b = 1; }; }; in s.a.b", Int);

// ==============================================================================
// `inherit (expr) name` — inherit from expression
// ==============================================================================

test_case!(
    inherit_from_expr,
    "let src = { x = 1; y = \"hi\"; }; in { inherit (src) x y; }",
    { "x": Int, "y": String }
);

// ==============================================================================
// Overload + Number interaction
// ==============================================================================

// Mixed arithmetic chain: `a * 2` constrains `a` to Number via `*`, then
// `(a * 2) + a` defers the `+` overload. The param is Number but the result
// of `+` is only bounded above by Number (not pinned), so it canonicalizes
// to a free var with Number upper bound — which the positive-position heuristic
// resolves to Number.
test_case!(arithmetic_chain, "a: a * 2 + a", (Number -> (# 0)));

// Negation of arithmetic result.
test_case!(negate_arithmetic, "a: -(a * 2)", (Number -> Number));

// ==============================================================================
// Deep polymorphism
// ==============================================================================

// Nested extrusion: `apply` composed with `id` should produce `Int` when
// applied to `id` and `5`.
test_case!(
    deep_polymorphism,
    "let apply = f: x: f x; id = x: x; in apply id 5",
    Int
);

// ==============================================================================
// Dynamic attrset keys
// ==============================================================================

// Dynamic select key constrains the result to the attrset's dyn_ty.
#[test]
fn dynamic_select_no_panic() {
    let ty = get_inferred_root("let s = { x = 1; }; k = \"x\"; in s.${k}");
    // Dynamic key can't resolve statically, but inference doesn't panic
    // and the result comes from the attrset's dyn_ty.
    let _ = ty;
}

// Dynamic intermediate keys in nested attr paths should not panic.
#[test]
fn dynamic_intermediate_attr_key() {
    let ty = get_inferred_root(r#"let k = "x"; in { ${k}.b = 1; }"#);
    // The dynamic key produces a dynamic entry whose value is { b = int }.
    // Just verify lowering and inference don't panic.
    let _ = ty;
}

// ==============================================================================
// `find_concrete` cycle safety (Review item #4)
// ==============================================================================

// Bidirectional constraint between two let bindings that reference each other.
// Tests whether find_concrete hits infinite recursion.
#[test]
fn bidirectional_let_cycle() {
    let ty = get_inferred_root("let a = b; b = a; in a");
    // Both a and b are in the same SCC group with circular references.
    // The type should be a free variable (no concrete info to discover).
    assert!(
        matches!(&ty, lang_ty::OutputTy::TyVar(_)),
        "bidirectional let should produce a free type variable, got: {ty}"
    );
}

// ==============================================================================
// Additional edge cases
// ==============================================================================

// Boolean inversion — `!` operator.
test_case!(bool_inversion, "!true", Bool);
test_case!(bool_inversion_lambda, "a: !a", (Bool -> Bool));

// List concatenation — homogeneous.
test_case!(list_concat, "[1 2] ++ [3 4]", [Int]);

// List concatenation — heterogeneous: `[1] ++ ["hi"]` should produce `[int | string]`.
#[test]
fn list_concat_heterogeneous() {
    let ty = get_inferred_root("[1] ++ [\"hi\"]");
    match &ty {
        lang_ty::OutputTy::List(elem) => {
            assert!(
                matches!(&*elem.0, lang_ty::OutputTy::Union(_)),
                "heterogeneous concat should have union element type, got: {}",
                elem.0
            );
        }
        _ => panic!("expected list type, got: {ty}"),
    }
}

// Has-attr operator.
test_case!(has_attr, "{ x = 1; } ? \"x\"", Bool);

// Assert expression — body type flows through.
test_case!(assert_body, "assert true; 42", Int);

// If-then-else with different branch types — produces a union.
#[test]
fn if_union_branches() {
    let ty = get_inferred_root("if true then 1 else \"hi\"");
    match &ty {
        lang_ty::OutputTy::Union(members) => {
            assert_eq!(members.len(), 2, "expected 2 union members, got: {ty}");
        }
        _ => panic!("expected union type from if branches, got: {ty}"),
    }
}

// ==============================================================================
// Type alias resolution (.tix stubs)
// ==============================================================================

// A doc comment annotation referencing a type alias resolves to the alias body.
#[test]
fn alias_resolution_in_annotation() {
    let registry = registry_from_tix("type MyRecord = { name: string, age: int };");

    // The annotation `foo :: MyRecord` should resolve to `{ name: string, age: int }`.
    let nix_src = indoc! { r#"
        let
            /**
                type: foo :: MyRecord
            */
            foo = { name = "alice"; age = 30; };
        in
        foo
    "# };

    let ty = get_inferred_root_with_aliases(nix_src, &registry);
    // With alias provenance tracking, the annotation wraps the type in Named.
    // Unwrap it to check the inner structural type.
    let inner = match &ty {
        lang_ty::OutputTy::Named(name, inner) => {
            assert_eq!(name.as_str(), "MyRecord");
            &*inner.0
        }
        other => other,
    };
    match inner {
        lang_ty::OutputTy::AttrSet(attr) => {
            assert!(attr.fields.contains_key("name"), "should have field name");
            assert!(attr.fields.contains_key("age"), "should have field age");
        }
        _ => panic!("expected attrset type (possibly wrapped in Named), got: {ty:?}"),
    }
}

// Global val declarations provide types for unresolved names.
#[test]
fn global_val_for_unresolved_name() {
    let registry =
        registry_from_tix("val mkDerivation :: { name: string, ... } -> { name: string };");

    let nix_src = indoc! { r#"
        mkDerivation { name = "hello"; }
    "# };

    let ty = get_inferred_root_with_aliases(nix_src, &registry);
    match &ty {
        lang_ty::OutputTy::AttrSet(attr) => {
            assert!(attr.fields.contains_key("name"), "should have field name");
        }
        _ => panic!("expected attrset type from mkDerivation return, got: {ty}"),
    }
}

// Global vals are polymorphic — each reference gets fresh type variables.
#[test]
fn global_val_polymorphism() {
    let registry = registry_from_tix("val id :: a -> a;");

    let nix_src = indoc! { r#"
        {
            int_result = id 42;
            str_result = id "hello";
        }
    "# };

    let ty = get_inferred_root_with_aliases(nix_src, &registry);
    match &ty {
        lang_ty::OutputTy::AttrSet(attr) => {
            let int_ty = attr.fields.get("int_result").expect("int_result field");
            let str_ty = attr.fields.get("str_result").expect("str_result field");
            assert_eq!(*int_ty.0, arc_ty!(Int), "id 42 should be int");
            assert_eq!(*str_ty.0, arc_ty!(String), "id \"hello\" should be string");
        }
        _ => panic!("expected attrset type, got: {ty}"),
    }
}

// Module-to-attrset alias: `module lib { ... }` creates alias "Lib".
alias_test_case!(
    module_alias_in_annotation,
    tix: r#"
        module lib {
            val id :: a -> a;
        }
    "#,
    nix: r#"
        let
            /**
                type: lib :: Lib
            */
            lib = { id = x: x; };
        in
        lib.id 42
    "#,
    Int
);

// ==============================================================================
// Nested attribute paths (implicit attrset desugaring)
// ==============================================================================

// `a.b = 1` desugars to `a = { b = 1; }`.
test_case!(
    nested_attr_simple,
    "{ a.b = 1; }",
    { "a": { "b": Int } }
);

// Multiple nested paths under the same prefix merge into one attrset.
test_case!(
    nested_attr_merge_siblings,
    "{ a.b = 1; a.c = \"hi\"; }",
    { "a": { "b": Int, "c": String } }
);

// Deep nesting: `a.b.c = 1` creates two levels of implicit attrsets.
test_case!(
    nested_attr_deep,
    "{ x.y.z = true; }",
    { "x": { "y": { "z": Bool } } }
);

// Explicit set merged with implicit nested path: `a.b = 1; a = { c = 2; };`
test_case!(
    nested_attr_merge_explicit,
    "{ a.b = 1; a = { c = 2; }; }",
    { "a": { "b": Int, "c": Int } }
);

// Nested paths inside a let-in binding.
test_case!(
    nested_attr_let,
    "let cfg.host = \"localhost\"; cfg.port = 8080; in cfg.host",
    String
);

// Selecting through an implicitly nested attrset.
test_case!(
    nested_attr_select,
    "let s = { a.b.c = 42; }; in s.a.b.c",
    Int
);

// ==============================================================================
// Multi-file import tests
// ==============================================================================

mod import_tests {
    use lang_ast::tests::MultiFileTestDatabase;
    use lang_ty::{arc_ty, OutputTy};
    use std::collections::{HashMap, HashSet};

    use crate::aliases::TypeAliasRegistry;
    use crate::check_file_with_imports;
    use crate::imports::resolve_imports;

    /// Infer a multi-file project, returning the root type and any import errors.
    fn check_multifile(files: &[(&str, &str)]) -> (OutputTy, Vec<crate::imports::ImportError>) {
        let (db, entry_file) = MultiFileTestDatabase::new(files);

        let module = lang_ast::module(&db, entry_file);
        let name_res = lang_ast::name_resolution(&db, entry_file);
        let aliases = TypeAliasRegistry::default();

        let mut in_progress = HashSet::new();
        let mut cache = HashMap::new();
        let resolution = resolve_imports(
            &db,
            entry_file,
            &module,
            &name_res,
            &aliases,
            &mut in_progress,
            &mut cache,
        );

        let errors = resolution.errors;

        let result = check_file_with_imports(&db, entry_file, &aliases, resolution.types)
            .expect("inference should succeed");

        let root_ty = result
            .expr_ty_map
            .get(module.entry_expr)
            .expect("root expr should have a type")
            .clone();

        (root_ty, errors)
    }

    fn get_multifile_root(files: &[(&str, &str)]) -> OutputTy {
        check_multifile(files).0
    }

    fn get_multifile_result(
        files: &[(&str, &str)],
    ) -> (OutputTy, Vec<crate::imports::ImportError>) {
        check_multifile(files)
    }

    // Import a file that evaluates to a literal int.
    #[test]
    fn import_literal_int() {
        let ty = get_multifile_root(&[("/main.nix", "import /foo.nix"), ("/foo.nix", "42")]);
        assert_eq!(ty, arc_ty!(Int));
    }

    // Import an attrset and select a field.
    #[test]
    fn import_attrset_select() {
        let ty = get_multifile_root(&[
            ("/main.nix", "let lib = import /lib.nix; in lib.x"),
            ("/lib.nix", "{ x = 1; y = \"hello\"; }"),
        ]);
        assert_eq!(ty, arc_ty!(Int));
    }

    // Import a file exporting a polymorphic function, used at different types.
    #[test]
    fn import_polymorphic_function() {
        let ty = get_multifile_root(&[
            (
                "/main.nix",
                r#"
                let id = import /id.nix;
                in {
                    a = id 1;
                    b = id "hello";
                }
                "#,
            ),
            ("/id.nix", "x: x"),
        ]);
        match &ty {
            OutputTy::AttrSet(attr) => {
                let a = attr.fields.get("a").expect("field a");
                let b = attr.fields.get("b").expect("field b");
                assert_eq!(*a.0, arc_ty!(Int), "id 1 should be int");
                assert_eq!(*b.0, arc_ty!(String), "id \"hello\" should be string");
            }
            _ => panic!("expected attrset, got: {ty}"),
        }
    }

    // Transitive imports: A → B → C.
    #[test]
    fn import_transitive() {
        let ty = get_multifile_root(&[
            ("/a.nix", "import /b.nix"),
            ("/b.nix", "import /c.nix"),
            ("/c.nix", "42"),
        ]);
        assert_eq!(ty, arc_ty!(Int));
    }

    // Diamond imports: A imports B and C, both import D.
    // D should be inferred only once (via cache).
    #[test]
    fn import_diamond() {
        let ty = get_multifile_root(&[
            (
                "/a.nix",
                r#"
                let
                    b = import /b.nix;
                    c = import /c.nix;
                in {
                    fromB = b;
                    fromC = c;
                }
                "#,
            ),
            ("/b.nix", "import /d.nix"),
            ("/c.nix", "import /d.nix"),
            ("/d.nix", "42"),
        ]);
        match &ty {
            OutputTy::AttrSet(attr) => {
                let from_b = attr.fields.get("fromB").expect("field fromB");
                let from_c = attr.fields.get("fromC").expect("field fromC");
                assert_eq!(*from_b.0, arc_ty!(Int));
                assert_eq!(*from_c.0, arc_ty!(Int));
            }
            _ => panic!("expected attrset, got: {ty}"),
        }
    }

    // Cyclic import: A → B → A should produce an error and degrade gracefully.
    #[test]
    fn import_cyclic() {
        let (ty, errors) =
            get_multifile_result(&[("/a.nix", "import /b.nix"), ("/b.nix", "import /a.nix")]);
        // At least one cyclic import error should be reported.
        assert!(
            errors
                .iter()
                .any(|e| matches!(&e.kind, crate::imports::ImportErrorKind::CyclicImport(_))),
            "expected cyclic import error, got: {:?}",
            errors.iter().map(|e| &e.kind).collect::<Vec<_>>()
        );
        // The type degrades to a free variable since the cycle can't be resolved.
        // As long as inference didn't panic, the test passes.
        let _ = ty;
    }

    // Non-literal import argument (variable) — should stay unconstrained.
    #[test]
    fn import_non_literal() {
        let ty = get_multifile_root(&[("/main.nix", "let p = /foo.nix; in import p")]);
        // `import p` where p is a variable — scanner can't resolve it,
        // so it falls through to the generic `import :: a -> b` builtin.
        assert!(
            matches!(ty, OutputTy::TyVar(_)),
            "non-literal import should produce a type variable, got: {ty}"
        );
    }

    // File not found — degrades to unconstrained type variable.
    #[test]
    fn import_file_not_found() {
        let (ty, errors) = get_multifile_result(&[("/main.nix", "import /nonexistent.nix")]);
        assert!(
            errors
                .iter()
                .any(|e| matches!(&e.kind, crate::imports::ImportErrorKind::FileNotFound(_))),
            "expected file not found error, got: {:?}",
            errors.iter().map(|e| &e.kind).collect::<Vec<_>>()
        );
        // Import without resolution falls through to the generic builtin.
        assert!(
            matches!(ty, OutputTy::TyVar(_)),
            "unresolved import should produce a type variable, got: {ty}"
        );
    }

    // Import a string.
    #[test]
    fn import_string() {
        let ty = get_multifile_root(&[
            ("/main.nix", "import /greeting.nix"),
            ("/greeting.nix", "\"hello world\""),
        ]);
        assert_eq!(ty, arc_ty!(String));
    }

    // Import a lambda and apply it.
    #[test]
    fn import_lambda_apply() {
        let ty = get_multifile_root(&[
            ("/main.nix", "(import /add.nix) 1 2"),
            ("/add.nix", "a: b: a - b"),
        ]);
        // Subtraction (not overloaded like +) constrains operands to Number,
        // so the exported type is `number -> number -> number`.
        // Applying to two ints gives number (not pinned to int since the
        // imported OutputTy loses deferred overload context).
        assert_eq!(ty, arc_ty!(Number));
    }

    // Import with overloaded + produces unconstrained vars since deferred
    // overloads don't survive the OutputTy boundary between files.
    #[test]
    fn import_overloaded_add_limitation() {
        let ty = get_multifile_root(&[
            ("/main.nix", "(import /add.nix) 1 2"),
            ("/add.nix", "a: b: a + b"),
        ]);
        // The + overload in add.nix can't be resolved without concrete types,
        // and the deferred overload info is lost in the OutputTy export.
        // The result is a free type variable.
        assert!(
            matches!(ty, OutputTy::TyVar(_)),
            "overloaded + across files produces unconstrained var, got: {ty}"
        );
    }

    /// Verify that `ImportResolution.targets` maps Apply, fun (Reference), and
    /// arg (Literal) ExprIds to the resolved target path for each import.
    #[test]
    fn import_targets_populated() {
        use lang_ast::{Expr, Literal};
        use std::path::PathBuf;

        let (db, entry_file) =
            MultiFileTestDatabase::new(&[("/main.nix", "import /lib.nix"), ("/lib.nix", "42")]);

        let module = lang_ast::module(&db, entry_file);
        let name_res = lang_ast::name_resolution(&db, entry_file);
        let aliases = TypeAliasRegistry::default();

        let mut in_progress = HashSet::new();
        let mut cache = HashMap::new();
        let resolution = resolve_imports(
            &db,
            entry_file,
            &module,
            &name_res,
            &aliases,
            &mut in_progress,
            &mut cache,
        );

        // There should be exactly 3 target entries: Apply, fun (Reference), arg (Literal).
        assert_eq!(
            resolution.targets.len(),
            3,
            "expected 3 target entries (Apply + fun + arg), got {:?}",
            resolution.targets
        );

        // All three should point to the same target path.
        let target = PathBuf::from("/lib.nix");
        for path in resolution.targets.values() {
            assert_eq!(*path, target, "all targets should resolve to /lib.nix");
        }

        // Verify we have the right expression kinds mapped.
        let mut has_apply = false;
        let mut has_reference = false;
        let mut has_path_literal = false;
        for expr_id in resolution.targets.keys() {
            match &module[*expr_id] {
                Expr::Apply { .. } => has_apply = true,
                Expr::Reference(name) if name == "import" => has_reference = true,
                Expr::Literal(Literal::Path(_)) => has_path_literal = true,
                _ => {}
            }
        }
        assert!(has_apply, "targets should include the Apply expression");
        assert!(has_reference, "targets should include the import Reference");
        assert!(has_path_literal, "targets should include the path Literal");
    }
}

// ==============================================================================
// Named type alias preservation in hover display
// ==============================================================================

// A doc comment annotation referencing a type alias produces OutputTy::Named
// wrapping the expanded type, so hover display shows the alias name.
#[test]
fn alias_named_in_annotation() {
    let registry = registry_from_tix(
        r#"
        module lib {
            val id :: a -> a;
        }
    "#,
    );

    let nix_src = indoc! { r#"
        let
            /**
                type: lib :: Lib
            */
            lib = { id = x: x; };
        in
        lib
    "# };

    let ty = get_name_type_with_aliases(nix_src, "lib", &registry);
    // The type should be Named("Lib", ...) wrapping the structural attrset.
    assert!(
        matches!(&ty, OutputTy::Named(name, _) if name == "Lib"),
        "annotated name should produce Named(\"Lib\", ...), got: {ty:?}"
    );
    // Display should show just the alias name.
    assert_eq!(format!("{ty}"), "Lib");
}

// When a let-binding's type flows from an annotated lambda parameter, the
// binding site should show the inferred type, not a bare free variable.
// Regression: `early_canonical` captured a bare TyVar before the lambda
// parameter annotation had propagated.
#[test]
fn binding_type_with_annotated_lambda_param() {
    let registry = registry_from_tix(
        r#"
        module lib {
            module strings {
                val concatStringsSep :: string -> [string] -> string;
            }
        }
    "#,
    );

    let nix_src = indoc! { r#"
        {
          /**
            type: lib :: Lib
          */
          lib,
        }:
        let
          foo = lib.strings.concatStringsSep " ";
        in
        foo []
    "# };

    let ty = get_name_type_with_aliases(nix_src, "foo", &registry);
    // foo is a partial application of concatStringsSep: [string] -> string
    assert!(
        matches!(&ty, OutputTy::Lambda { .. }),
        "foo binding should be a lambda, got: {ty:?}"
    );
}

// A global val returning a type alias wraps the return type in Named.
#[test]
fn alias_named_from_global_val_return() {
    let registry = registry_from_tix(
        r#"
        type Derivation = { name: string, system: string, ... };
        val mkDerivation :: { name: string, ... } -> Derivation;
    "#,
    );

    let nix_src = indoc! { r#"
        mkDerivation { name = "hello"; }
    "# };

    let ty = get_inferred_root_with_aliases(nix_src, &registry);
    assert!(
        matches!(&ty, OutputTy::Named(name, _) if name == "Derivation"),
        "mkDerivation return should produce Named(\"Derivation\", ...), got: {ty:?}"
    );
    assert_eq!(format!("{ty}"), "Derivation");
}

// ==============================================================================
// Diagnostic message format tests
// ==============================================================================

diagnostic_msg!(
    diag_type_mismatch_if_cond,
    "if 1 then true else false",
    contains "type mismatch"
);

diagnostic_msg!(
    diag_sub_string_msg,
    r#""hello" - 1"#,
    contains "type mismatch"
);

diagnostic_msg!(
    diag_missing_field_with_suggestion,
    "let s = { foo = 1; bar = 2; }; in s.bra",
    contains "did you mean `bar`"
);

diagnostic_msg!(
    diag_missing_field_shows_available,
    "let s = { foo = 1; bar = 2; }; in s.baz",
    contains "available fields"
);

diagnostic_msg!(
    diag_no_false_suggestion_for_distant_name,
    "let s = { foo = 1; }; in s.completely_different",
    not contains "did you mean"
);

diagnostic_msg!(
    diag_attrset_merge_error,
    "1 // 2",
    contains "cannot merge"
);

diagnostic_msg!(
    diag_missing_field_through_function,
    "let f = { x }: x; in f { y = 1; }",
    contains "missing field `x`"
);

// Let-binding flow: `let drv = mkDerivation { ... }; in drv` preserves the alias.
#[test]
fn alias_named_flows_through_let() {
    let registry = registry_from_tix(
        r#"
        type Derivation = { name: string, system: string, ... };
        val mkDerivation :: { name: string, ... } -> Derivation;
    "#,
    );

    let nix_src = indoc! { r#"
        let
            drv = mkDerivation { name = "my-package"; };
        in
        drv
    "# };

    let ty = get_inferred_root_with_aliases(nix_src, &registry);
    assert!(
        matches!(&ty, OutputTy::Named(name, _) if name == "Derivation"),
        "let-bound drv should preserve Named(\"Derivation\", ...), got: {ty:?}"
    );
    assert_eq!(format!("{ty}"), "Derivation");
}

// ==============================================================================
// Context args (tix.toml / doc comment context)
// ==============================================================================

use comment_parser::ParsedTy;
use smol_str::SmolStr;
use std::collections::HashMap;

/// Helper to type-check a string with context args applied to the root lambda.
fn check_str_with_context(
    src: &str,
    context_args: HashMap<SmolStr, ParsedTy>,
) -> (Module, crate::CheckResult) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::with_builtins(),
        HashMap::new(),
        context_args,
    );
    (module, result)
}

fn get_inferred_root_with_context(src: &str, context_args: HashMap<SmolStr, ParsedTy>) -> OutputTy {
    let (module, result) = check_str_with_context(src, context_args);
    result
        .inference
        .expect("inference should succeed")
        .expr_ty_map
        .get(module.entry_expr)
        .expect("root expr should have a type")
        .clone()
}

fn nixos_context_args() -> HashMap<SmolStr, ParsedTy> {
    let mut registry = TypeAliasRegistry::with_builtins();
    registry.load_context_by_name("nixos").unwrap().unwrap()
}

/// NixOS module pattern: `{ config, lib, pkgs, ... }: lib.id 42`
/// With context args, `lib` should be typed as `Lib` so `lib.id` resolves.
#[test]
fn context_args_type_root_lambda_lib() {
    let ctx = nixos_context_args();
    let nix_src = indoc! { "
        { config, lib, pkgs, ... }: lib.id 42
    " };

    let ty = get_inferred_root_with_context(nix_src, ctx);
    // The root lambda returns `lib.id 42` which should be `int`.
    match &ty {
        OutputTy::Lambda { body, .. } => {
            assert_eq!(
                *body.0,
                arc_ty!(Int),
                "lib.id 42 should infer as int with context, got: {}",
                body.0
            );
        }
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

/// Context args should only apply to the root lambda, not inner lambdas.
#[test]
fn context_args_do_not_apply_to_inner_lambda() {
    let ctx = nixos_context_args();
    let nix_src = indoc! { "
        { lib, ... }:
        let
            inner = { lib, ... }: lib;
        in
        inner { lib = 42; }
    " };

    let ty = get_inferred_root_with_context(nix_src, ctx);
    // The root lambda's result is `inner { lib = 42; }`.
    // `inner` is `{ lib, ... }: lib` — an inner lambda that should NOT get
    // context args. So `inner { lib = 42; }` should infer as `int`.
    match &ty {
        OutputTy::Lambda { body, .. } => {
            assert_eq!(
                *body.0,
                arc_ty!(Int),
                "inner lambda should not get context args, got: {}",
                body.0
            );
        }
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

/// Context args with unknown field names should be silently ignored.
#[test]
fn context_args_unknown_fields_ignored() {
    let mut ctx = nixos_context_args();
    // Add a field that doesn't exist in the lambda pattern.
    ctx.insert(
        SmolStr::from("nonexistent_arg"),
        comment_parser::known_ty!(int),
    );

    let nix_src = indoc! { "
        { config, lib, ... }: lib.id 42
    " };

    // Should not error — extra context args for names not in the pattern
    // are simply skipped.
    let ty = get_inferred_root_with_context(nix_src, ctx);
    match &ty {
        OutputTy::Lambda { body, .. } => {
            assert_eq!(*body.0, arc_ty!(Int));
        }
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

/// Verify doc comments attach to lambda expressions inside let bindings.
#[test]
fn doc_comment_attaches_to_lambda_expr() {
    let nix_src = indoc! { r#"
        let
            mkModule =
                /** context: nixos */
                { config, lib, pkgs, ... }: lib.id 42;
        in
        mkModule
    "# };

    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let mod_ = module(&db, file);

    // Find the lambda expression.
    let lambda_id = mod_
        .exprs()
        .find_map(|(id, expr)| match expr {
            lang_ast::Expr::Lambda { .. } => Some(id),
            _ => None,
        })
        .expect("should have a lambda");

    let docs = mod_.type_dec_map.docs_for_expr(lambda_id);
    assert!(
        docs.is_some(),
        "lambda should have doc comments, but docs_for_expr returned None. \
         All expr docs: {:?}",
        mod_.exprs()
            .filter_map(|(id, _)| mod_.type_dec_map.docs_for_expr(id).map(|d| (id, d)))
            .collect::<Vec<_>>()
    );
}

/// Doc comment `/** context: nixos */` on a non-root lambda should apply types.
/// The comment must be placed between `=` and the lambda (on the expression),
/// not before the binding name (which would be a name annotation).
#[test]
fn doc_comment_context_on_inner_lambda() {
    let nix_src = indoc! { "
        let
            mkModule =
                /** context: nixos */
                { config, lib, pkgs, ... }: lib.id 42;
        in
        mkModule
    " };

    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::with_builtins(),
        HashMap::new(),
        HashMap::new(), // no file-level context
    );

    let inference = result.inference.expect("inference should succeed");

    // Look up mkModule's type — it's a let binding, so check name_ty_map.
    let mk_module_ty = mod_
        .names()
        .find_map(|(id, name)| {
            if name.text == "mkModule" {
                inference.name_ty_map.get(id)
            } else {
                None
            }
        })
        .expect("mkModule should have a type");

    // mkModule is a lambda, its body should return int (lib.id 42).
    match mk_module_ty {
        OutputTy::Lambda { body, .. } => {
            assert_eq!(
                *body.0,
                arc_ty!(Int),
                "doc comment context should type lib.id 42 as int, got: {}",
                body.0
            );
        }
        _ => panic!("expected lambda, got: {mk_module_ty}"),
    }
}

/// Both file-level context and doc comment context on the same lambda —
/// file-level wins for the root expression.
#[test]
fn file_level_context_overrides_doc_comment_for_root() {
    let ctx = nixos_context_args();
    let nix_src = indoc! { "
        { lib, ... }: lib.id 42
    " };

    // Even without a doc comment, the file-level context should type `lib`.
    let ty = get_inferred_root_with_context(nix_src, ctx);
    match &ty {
        OutputTy::Lambda { body, .. } => {
            assert_eq!(*body.0, arc_ty!(Int));
        }
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

/// Context args should preserve alias provenance on pattern fields.
/// Without this, `config` would be inferred as a plain attrset instead of
/// `Named("NixosConfig", ...)`, breaking doc lookups by alias name.
#[test]
fn context_args_preserve_alias_provenance() {
    // Load context stubs into a registry so the NixosConfig alias is
    // available during type inference (mirrors what the LSP does — the
    // registry must contain both the type aliases and val declarations).
    let mut registry = TypeAliasRegistry::with_builtins();
    let ctx = registry.load_context_by_name("nixos").unwrap().unwrap();

    let nix_src = indoc! { "
        { config, ... }: config
    " };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let module = module(&db, file);
    let result = crate::check_file_collecting(&db, file, &registry, HashMap::new(), ctx);
    let inference = result.inference.expect("inference should succeed");

    // The `config` pattern field should be typed as Named("NixosConfig", ...)
    // thanks to the context arg `val config :: NixosConfig` and alias provenance.
    let config_name_id = module
        .names()
        .find(|(_, n)| n.text == "config")
        .map(|(id, _)| id)
        .expect("config name should exist");
    let config_ty = inference
        .name_ty_map
        .get(config_name_id)
        .expect("config should have an inferred type");

    match config_ty {
        OutputTy::Named(name, _) => {
            assert_eq!(
                name.as_str(),
                "NixosConfig",
                "config should be Named(\"NixosConfig\", ...), got Named(\"{name}\", ...)"
            );
        }
        other => panic!("config should be Named(\"NixosConfig\", ...), got: {other}"),
    }
}

/// Context args should type `config` as an open attrset.
#[test]
fn context_args_config_is_open_attrset() {
    let ctx = nixos_context_args();
    let nix_src = indoc! { "
        { config, ... }: config.networking
    " };

    let ty = get_inferred_root_with_context(nix_src, ctx);
    // config is typed as `{ ... }` (open attrset), so `config.networking`
    // should not produce a type error — it returns a free variable.
    match &ty {
        OutputTy::Lambda { body, .. } => {
            // The body should be a TyVar (since config is open and networking
            // is unconstrained).
            assert!(
                matches!(&*body.0, OutputTy::TyVar(_)),
                "config.networking should be a free type var, got: {}",
                body.0
            );
        }
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

// =============================================================================
// Optional fields (pattern defaults)
// =============================================================================

// Calling a function with an optional field, omitting the optional field.
test_case!(optional_field_omitted,
    "({ x, y ? 0 }: x + y) { x = 1; }",
    Int
);

// Calling a function with an optional field, providing the optional field.
test_case!(optional_field_provided,
    "({ x, y ? 0 }: x + y) { x = 1; y = 2; }",
    Int
);

// Optional field combined with ellipsis.
test_case!(optional_field_with_ellipsis,
    "({ x, y ? 0, ... }: x + y) { x = 1; }",
    Int
);

// Multiple optional fields, all omitted.
test_case!(multiple_optional_fields_omitted,
    "({ x, y ? 0, z ? 1 }: x + y + z) { x = 1; }",
    Int
);

/// Optional field with null default.
#[test]
fn optional_field_default_null() {
    let nix_src = r#"({ name ? null }: name) {}"#;
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!(Null));
}

/// Required fields still error when missing.
#[test]
fn required_field_still_errors() {
    let nix_src = "({ x, y }: x + y) { x = 1; }";
    let err = get_check_error(nix_src);
    assert!(
        matches!(err, TixDiagnosticKind::MissingField { ref field, .. } if field == "y"),
        "expected MissingField error for 'y', got: {err:?}"
    );
}

/// Display format shows `?` for optional fields.
#[test]
fn optional_field_display() {
    let nix_src = "{ x, y ? 0 }: x + y";
    let ty = get_inferred_root(nix_src);
    let display = format!("{ty}");
    assert!(
        display.contains("y?:"),
        "expected 'y?:' in display, got: {display}"
    );
    // `x` should NOT have `?`
    assert!(
        display.contains("x:") && !display.contains("x?:"),
        "expected 'x:' without '?' in display, got: {display}"
    );
}
