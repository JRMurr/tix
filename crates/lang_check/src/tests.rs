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
// Ordering operators constrain both sides to the same type, so `arg.foo < 10`
// forces foo to Int and `arg.bar < ./test.nix` forces bar to Path.
test_case!(
    row_poly,
    "
        arg: (arg.foo < 10) && (arg.bar < ./test.nix)
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

// ==============================================================================
// Line comment annotations (# type: name :: Type)
// ==============================================================================

// Line comments with `type:` prefix should work identically to /** type: */ block comments.
test_case!(
    line_comment_annotation_pat_field,
    "
    let
        f = {
            # type: x :: int
            x,
            # type: y :: string
            y
        }: { inherit x y; };
    in
    f { x = 1; y = \"hello\"; }
    ",
    { "x": (Int), "y": (String) }
);

test_case!(
    line_comment_annotation_constrains_body,
    "
    let
        f = {
            # type: x :: int
            x
        }: x + 1;
    in
    f { x = 42; }
    ",
    Int
);

test_case!(
    line_comment_annotation_let_binding,
    "
    let
        # type: foo :: string
        foo = ''hi'';
    in
    foo
    ",
    String
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
// Boolean operators
// ==============================================================================

test_case!(bool_and, "true && false", Bool);
test_case!(bool_or, "true || false", Bool);

// Nix `->` is boolean implication (not lambda). Must use let-bound
// variables because `true -> false` would parse as a lambda.
test_case!(bool_implication, "let a = true; b = false; in a -> b", Bool);

// Polymorphic boolean operators: both operands constrained to Bool.
test_case!(bool_and_vars, "a: b: a && b", (Bool -> Bool -> Bool));
test_case!(bool_or_vars, "a: b: a || b", (Bool -> Bool -> Bool));

// Non-bool operand is a type error.
error_case!(
    bool_and_non_bool_lhs,
    "1 && true",
    matches TixDiagnosticKind::TypeMismatch { .. }
);
error_case!(
    bool_or_non_bool_rhs,
    "true || 1",
    matches TixDiagnosticKind::TypeMismatch { .. }
);

// ==============================================================================
// Comparison operators
// ==============================================================================

// Ordering operators: both sides must be the same type, result is Bool.
test_case!(compare_less, "1 < 2", Bool);
test_case!(compare_greater_eq, "1.0 >= 2.0", Bool);
test_case!(compare_string, r#""a" < "b""#, Bool);

// Ordering on different types is a type error (bidirectional constraint).
error_case!(
    compare_cross_type,
    r#"1 < "hi""#,
    matches TixDiagnosticKind::TypeMismatch { .. }
);

// Equality operators: no type constraints, result is always Bool.
test_case!(equality_same_type, "1 == 2", Bool);
test_case!(equality_cross_type, r#"1 == "hi""#, Bool);
test_case!(inequality, "1 != 2", Bool);

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
        lang_ty::OutputTy::List(elem) => match &*elem.0 {
            lang_ty::OutputTy::Union(members) => {
                assert_eq!(
                    members.len(),
                    3,
                    "expected 3 union members, got: {}",
                    elem.0
                );
                let has_int = members.iter().any(|m| *m.0 == arc_ty!(Int));
                let has_string = members.iter().any(|m| *m.0 == arc_ty!(String));
                let has_bool = members.iter().any(|m| *m.0 == arc_ty!(Bool));
                assert!(has_int, "union should contain Int, got: {}", elem.0);
                assert!(has_string, "union should contain String, got: {}", elem.0);
                assert!(has_bool, "union should contain Bool, got: {}", elem.0);
            }
            other => panic!("expected union element type, got: {other}"),
        },
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
    // Dynamic key can't resolve statically — the result comes from the
    // attrset's dyn_ty, which is unconstrained (type variable).
    assert!(
        matches!(ty, OutputTy::TyVar(_)),
        "dynamic select should produce type var, got: {ty}"
    );
}

// Dynamic intermediate keys in nested attr paths should not panic.
#[test]
fn dynamic_intermediate_attr_key() {
    let ty = get_inferred_root(r#"let k = "x"; in { ${k}.b = 1; }"#);
    // The dynamic key produces an attrset with a dynamic entry whose
    // value is { b = int }.
    assert!(
        matches!(ty, OutputTy::AttrSet(_)),
        "dynamic intermediate key should produce attrset, got: {ty}"
    );
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
test_case!(
    optional_field_omitted,
    "({ x, y ? 0 }: x + y) { x = 1; }",
    Int
);

// Calling a function with an optional field, providing the optional field.
test_case!(
    optional_field_provided,
    "({ x, y ? 0 }: x + y) { x = 1; y = 2; }",
    Int
);

// Optional field combined with ellipsis.
test_case!(
    optional_field_with_ellipsis,
    "({ x, y ? 0, ... }: x + y) { x = 1; }",
    Int
);

// Multiple optional fields, all omitted.
test_case!(
    multiple_optional_fields_omitted,
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

/// Inline call where a null-default field is provided with an attrset.
/// The return type is the union of the default (null) and the provided value.
#[test]
fn null_default_field_provided_attrset_inline() {
    let nix_src = r#"({ config ? null }: config) { config = { foo = 1; }; }"#;
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!(union!(Null, { "foo": Int })));
}

/// Let-bound function with null-default field, called with an attrset.
/// After generalization the call site instantiates the polymorphic type,
/// so the result reflects the provided value without the null union.
#[test]
fn null_default_field_provided_attrset_let_bound() {
    let nix_src = indoc! {"
        let
          f = { config ? null }: config;
        in f { config = { foo = 1; }; }
    "};
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!({ "foo": Int }));
}

/// Let-bound function with null-default field, called without the field.
/// After polymorphic generalization, the call instantiates a fresh type
/// variable — the null default is baked into the function's bounds but
/// doesn't surface at this call site.
#[test]
fn null_default_field_omitted_let_bound() {
    let nix_src = indoc! {"
        let
          f = { config ? null }: config;
        in f {}
    "};
    let ty = get_inferred_root(nix_src);
    assert!(
        matches!(ty, OutputTy::TyVar(_)),
        "expected a free type variable, got: {ty:?}"
    );
}

/// Multiple call sites: one provides an attrset, the other omits the field.
/// Each call site gets its own instantiation of the polymorphic function.
#[test]
fn null_default_field_multiple_call_sites() {
    let nix_src = indoc! {"
        let
          f = { config ? null }: config;
          a = f { config = { foo = 1; }; };
          b = f {};
        in { inherit a b; }
    "};
    let ty = get_inferred_root(nix_src);
    let display = format!("{ty}");
    // `a` gets the provided attrset type, `b` gets a fresh type variable
    // (the polymorphic instantiation doesn't constrain it beyond the default).
    assert!(
        display.contains("a: { foo: int }"),
        "expected 'a: {{ foo: int }}' in display, got: {display}"
    );
}

/// Field access on a null-default parameter is a type error because
/// the parameter could be null. This is correct — narrowing (e.g.,
/// `if config != null then config.foo else ...`) is needed for safety.
#[test]
fn null_default_field_access_is_type_error() {
    let nix_src = r#"({ config ? null }: config.foo) { config = { foo = 1; }; }"#;
    let err = get_check_error(nix_src);
    assert!(
        matches!(err, TixDiagnosticKind::TypeMismatch { .. }),
        "expected TypeMismatch error, got: {err:?}"
    );
}

/// Null-default alongside a required field — the required field still
/// participates in the result while the optional one unions with null.
#[test]
fn null_default_with_required_field_inline() {
    let nix_src = r#"({ config ? null, name }: { inherit config name; }) { name = "hello"; }"#;
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!({ "config": Null, "name": String }));
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

// =============================================================================
// Select-or-default (`x.field or default`)
// =============================================================================

/// `x.field or default` on a closed attrset missing the field should succeed.
#[test]
fn select_or_default_missing_field() {
    let nix_src = r#"let s = { x = 1; }; in s.y or "fallback""#;
    let ty = get_inferred_root(nix_src);
    // `y` is provably absent, so only the default contributes.
    assert_eq!(ty, arc_ty!(String));
}

/// `x.field or default` on a closed attrset where the field IS present.
#[test]
fn select_or_default_field_present() {
    let nix_src = r#"let s = { x = 1; }; in s.x or "fallback""#;
    let ty = get_inferred_root(nix_src);
    // Both the field type (int) and default type (string) contribute.
    assert_eq!(ty, arc_ty!(union!(Int, String)));
}

/// Multi-segment path with `or`: `x.a.b or default` where x = {}.
#[test]
fn select_or_default_deep_path_missing() {
    let nix_src = "let s = {}; in s.a.b or 0";
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!(Int));
}

/// `builtins.tryEval` pattern: accessing a field that doesn't exist in the
/// return type, with `or` fallback.
#[test]
fn select_or_default_tryeval_absent_field() {
    // tryEval returns { success: bool, value: a } — no `error` field.
    let nix_src = r#"let r = builtins.tryEval 1; in r.error or "no error""#;
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!(String));
}

/// `builtins.tryEval` pattern: accessing `.value` with `or` fallback.
#[test]
fn select_or_default_tryeval_present_field() {
    let nix_src = "let r = builtins.tryEval 1; in r.value or null";
    let ty = get_inferred_root(nix_src);
    assert_eq!(ty, arc_ty!(union!(Int, Null)));
}

/// Select WITHOUT `or` on a closed attrset missing the field should still error.
#[test]
fn select_no_default_missing_field_errors() {
    let nix_src = "let s = { x = 1; }; in s.y";
    let err = get_check_error(nix_src);
    assert!(
        matches!(err, TixDiagnosticKind::MissingField { ref field, .. } if field == "y"),
        "expected MissingField error for 'y', got: {err:?}"
    );
}

/// `or` on an open attrset — should always succeed, field type is a variable.
#[test]
fn select_or_default_open_attrset() {
    let nix_src = r#"x: x.missing or "default""#;
    let ty = get_inferred_root(nix_src);
    // The function should infer without error. The parameter is open
    // (field access makes it { missing?: a, ... }) and result is a | string.
    match &ty {
        OutputTy::Lambda { .. } => {} // success — no error
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

// ==============================================================================
// Type narrowing — null guards
// ==============================================================================

/// Helper: extract param and body from a lambda OutputTy, panicking otherwise.
fn unwrap_lambda(ty: &OutputTy) -> (&OutputTy, &OutputTy) {
    match ty {
        OutputTy::Lambda { param, body } => (&param.0, &body.0),
        _ => panic!("expected lambda type, got: {ty}"),
    }
}

/// `if x == null then null else x.name` — the else-branch narrows x to
/// non-null (fresh var), so field access succeeds. The body should be
/// null (the else-branch's field access produces an unconstrained var
/// that collapses to bottom in positive position, leaving just null).
#[test]
fn narrow_null_eq_else_field_access() {
    let nix = r#"x: if x == null then null else x.name"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // The unconstrained field var from x.name has no lower bounds, so
    // in positive position it's bottom and `null | bottom = null`.
    assert_eq!(*body, arc_ty!(Null), "body should be null");
}

/// `if x != null then x.name else "default"` — then-branch narrows x to
/// non-null, so field access succeeds. The unconstrained field var
/// collapses, leaving just string from the else-branch.
#[test]
fn narrow_null_neq_then_field_access() {
    let nix = r#"x: if x != null then x.name else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// `if isNull x then 0 else x.y` — isNull builtin narrowing.
/// Then-branch returns int, else-branch's unconstrained var collapses.
#[test]
fn narrow_isnull_builtin() {
    let nix = "x: if isNull x then 0 else x.y";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// `if builtins.isNull x then 0 else x.y` — qualified builtin.
/// Same as isNull, just accessed through `builtins.`.
#[test]
fn narrow_builtins_isnull() {
    let nix = "x: if builtins.isNull x then 0 else x.y";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// `if !isNull x then x.y else 0` — negation flips narrowing.
/// Same result as isNull but with branches swapped.
#[test]
fn narrow_negated_isnull() {
    let nix = "x: if !(isNull x) then x.y else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// `assert x != null; x.name` — assert narrows body so field access on
/// the non-null branch succeeds. The body type comes from x.name only
/// (assert doesn't produce a union — it just constrains the body).
#[test]
fn narrow_assert_not_null() {
    let nix = "x: assert x != null; x.name";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Assert narrows x to non-null in the body. The result is whatever
    // x.name resolves to — a free type variable (no union with null).
    assert!(
        !matches!(body, OutputTy::Primitive(PrimitiveTy::Null)),
        "assert-narrowed body should not be null, got: {body}"
    );
    // Should be a single type (TyVar from the field access), not a union.
    assert!(
        matches!(body, OutputTy::TyVar(_)),
        "assert-narrowed body should be a type variable (from field access), got: {body}"
    );
}

/// Then-branch of `x == null` should narrow x to null.
/// `x: if x == null then x else 1` → body is null | int.
#[test]
fn narrow_null_eq_then_is_null() {
    let nix = indoc! {"
        x: if x == null then x else 1
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // x in the then-branch is narrowed to null, else-branch returns int.
    match body {
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Null))),
                "body should contain null, got: {body}"
            );
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Int))),
                "body should contain int, got: {body}"
            );
            assert_eq!(members.len(), 2, "expected null | int, got: {body}");
        }
        _ => panic!("expected union (null | int), got: {body}"),
    }
}

/// Regression: `if true then 1 else "hi"` should still produce a union
/// (narrowing shouldn't interfere when condition isn't a type guard).
#[test]
fn narrow_no_interference_with_non_guard() {
    let ty = get_inferred_root(r#"if true then 1 else "hi""#);
    match &ty {
        OutputTy::Union(members) => {
            assert_eq!(members.len(), 2, "expected 2 union members, got: {ty}");
        }
        _ => panic!("expected union type, got: {ty}"),
    }
}

/// Nested narrowing: inner if narrows same variable further.
/// Both branches of the inner if access x.y, so the field access must
/// succeed in both narrowed scopes.
#[test]
fn narrow_nested_same_var() {
    let nix = r#"x: if x != null then (if x != null then x.y else 0) else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Outer else: 0 (int). Outer then: inner if with x.y | 0.
    // The overall body should contain int.
    match body {
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Int))),
                "nested narrowing body should contain int, got: {body}"
            );
        }
        // If the checker resolves everything to int, that's also fine.
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        _ => panic!("expected body containing int, got: {body}"),
    }
}

/// `null == x` — null on the left side should also work.
/// `x: if null == x then 0 else x.y` — same as isNull test.
#[test]
fn narrow_null_on_lhs() {
    let nix = "x: if null == x then 0 else x.y";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// Both branches produce concrete types: `if x == null then "was null" else 42`.
/// Body should be a union of string and int.
#[test]
fn narrow_null_guard_concrete_branches() {
    let nix = r#"x: if x == null then "was null" else 42"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    match body {
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::String))),
                "body should contain string, got: {body}"
            );
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Int))),
                "body should contain int, got: {body}"
            );
        }
        _ => panic!("expected union (string | int), got: {body}"),
    }
}

/// `==` is a total function in Nix — it doesn't constrain operand types.
/// So `x == null` doesn't force null into x's bounds, and `x.name` succeeds
/// (x is unconstrained, field access just constrains it to an open attrset).
#[test]
fn equality_does_not_constrain_operands() {
    let nix = "x: (x == null) && x.name";
    let ty = get_inferred_root(nix);
    // x is unconstrained by ==, so x.name constrains x to { name: a, ... }
    // and && returns bool.
    let (_, body) = unwrap_lambda(&ty);
    assert!(
        matches!(body, OutputTy::Primitive(PrimitiveTy::Bool)),
        "equality should not constrain operands, got: {ty}"
    );
}

/// Cross-type equality is valid in Nix: `1 == "hi"` → false.
/// The type checker should accept it and infer bool.
#[test]
fn cross_type_equality_succeeds() {
    let ty = get_inferred_root(r#"1 == "hi""#);
    assert!(
        matches!(&ty, OutputTy::Primitive(PrimitiveTy::Bool)),
        "cross-type equality should infer bool, got: {ty}"
    );
}

/// Equality doesn't constrain a variable: `let _ = x == null; in x.name`
/// should succeed because `==` imposes no type relationship.
#[test]
fn equality_leaves_variable_unconstrained() {
    let nix = "x: let _ = x == null; in x.name";
    let ty = get_inferred_root(nix);
    let (_, body) = unwrap_lambda(&ty);
    // x.name succeeds — x gets constrained to { name: a, ... } by the
    // field access, not by the equality comparison.
    assert!(
        !matches!(body, OutputTy::Primitive(PrimitiveTy::Null)),
        "x should not be constrained to null by ==, got: {ty}"
    );
}

/// Ordering operators DO error on cross-type comparisons at runtime,
/// so the type checker should reject them.
#[test]
fn ordering_constrains_cross_type_error() {
    let err = get_check_error(r#"1 < "hi""#);
    assert!(
        matches!(err, TixDiagnosticKind::TypeMismatch { .. }),
        "ordering cross-type should error, got: {err:?}"
    );
}

/// `if x == null then x else "not null"` — then-branch narrows x to
/// null, else-branch returns a string literal. Body should be null | string.
#[test]
fn narrow_null_eq_then_narrowed_else_concrete() {
    let nix = r#"x: if x == null then x else "not null""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then: x is narrowed to null. Else: string literal.
    match body {
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Null))),
                "body should contain null from then-branch, got: {body}"
            );
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::String))),
                "body should contain string from else-branch, got: {body}"
            );
            assert_eq!(members.len(), 2, "expected null | string, got: {body}");
        }
        _ => panic!("expected union (null | string), got: {body}"),
    }
}

/// Narrowing + field access with a concrete result: else-branch accesses
/// a field and adds 1, giving a concrete type in the union.
#[test]
fn narrow_field_access_then_arithmetic() {
    let nix = indoc! {"
        x:
        if x == null then 0
        else x.count + 1
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then: 0 (int). Else: x.count + 1 — the + resolves with int on the
    // right, so x.count is constrained to Number. Result is Number.
    // The union of int and Number should simplify.
    match body {
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        OutputTy::Primitive(PrimitiveTy::Number) => {}
        OutputTy::Union(members) => {
            // All members should be numeric.
            for m in members {
                assert!(
                    matches!(
                        &*m.0,
                        OutputTy::Primitive(PrimitiveTy::Int)
                            | OutputTy::Primitive(PrimitiveTy::Number)
                            | OutputTy::Primitive(PrimitiveTy::Float)
                    ),
                    "all union members should be numeric, got: {body}"
                );
            }
        }
        _ => panic!("expected numeric body type, got: {body}"),
    }
}

// ==========================================================================
// Regression: polymorphic builtin wrappers
// ==========================================================================
//
// When a user-defined function wraps a builtin (passing multiple arguments
// through), each call site must get an independent instantiation. Previously,
// pre-allocated expression-slot TyIds at level 0 created a back-channel
// through which use-site constraints leaked back to the original polymorphic
// variables, causing type contamination between call sites.

test_case!(
    wrapper_foldl_int_and_list,
    "
        let
          myFoldl = op: acc: builtins.foldl' op acc;
          intResult = myFoldl (c: x: c + 1) 0 [1 2 3];
          listResult = myFoldl (acc: e: acc ++ [ e ]) [ ] [1 2 3];
        in
          { inherit intResult listResult; }
    ",
    {
        "intResult": (Int),
        "listResult": [Int]
    }
);

test_case!(
    wrapper_map_int_and_string,
    "
        let
          myMap = f: xs: builtins.map f xs;
          a = myMap (x: x + 1) [1 2 3];
          b = myMap (x: x + \"!\") [\"hi\" \"bye\"];
        in
          { inherit a b; }
    ",
    {
        "a": [Int],
        "b": [String]
    }
);

/// Regression test: nixpkgs lib/lists.nix defines `foldl'` as a wrapper
/// around `builtins.foldl'` (with a `builtins.seq` call). Both `count`
/// (with int accumulator) and `unique` (with list accumulator) call this
/// wrapper. The type of `count` must not contaminate `unique` or vice versa.
#[test]
fn wrapper_foldl_like_nixpkgs() {
    let src = indoc! {"
        let
          foldl' = op: acc: builtins.seq acc (builtins.foldl' op acc);
          count = pred: foldl' (c: x: if pred x then c + 1 else c) 0;
          unique = foldl' (acc: e: if builtins.elem e acc then acc else acc ++ [ e ]) [ ];
        in
          { inherit count unique; }
    "};
    let (module, result) = check_str(src);
    let inference = result.expect("should not produce a type error");
    let root = inference
        .expr_ty_map
        .get(module.entry_expr)
        .expect("root type");

    // Verify the root is an attrset — the key assertion is that inference
    // succeeds without the "expected [X], got int" errors that occurred
    // before the fix.
    match root {
        OutputTy::AttrSet { .. } => {}
        other => panic!("expected attrset, got: {other}"),
    }
}

// ==============================================================================
// Type narrowing — hasAttr (`?`) guards
// ==============================================================================

/// `if x ? name then x.name else "default"` — the then-branch narrows x to
/// have the `name` field, so field access succeeds without error.
#[test]
fn narrow_hasattr_then_field_access() {
    let nix = r#"x: if x ? name then x.name else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then-branch: x.name (unconstrained field var → bottom in positive pos).
    // Else-branch: "default" (string). Union collapses to string.
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// Chained hasattr: `if x ? a then x.a else if x ? b then x.b else null`.
/// Each branch narrows x independently.
#[test]
fn narrow_hasattr_chained() {
    let nix = r#"x: if x ? a then x.a else if x ? b then x.b else null"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // All field vars are unconstrained → bottom. The else-else is null.
    // Union of bottom | bottom | null = null.
    assert_eq!(*body, arc_ty!(Null), "chained hasattr body should be null");
}

/// `if !(x ? name) then "default" else x.name` — negation flips narrowing,
/// so the else-branch gets the HasField narrowing.
#[test]
fn narrow_hasattr_negated() {
    let nix = r#"x: if !(x ? name) then "default" else x.name"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "negated hasattr body should be string"
    );
}

/// `assert x ? name; x.name` — assert narrows the body so field access
/// on x succeeds.
#[test]
fn narrow_hasattr_assert() {
    let nix = "x: assert x ? name; x.name";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Assert applies then-branch narrowing. x.name produces a type var.
    assert!(
        matches!(body, OutputTy::TyVar(_)),
        "assert-narrowed hasattr body should be a type variable, got: {body}"
    );
}

/// Dynamic key like `x ? ${k}` should not crash — it just produces no
/// narrowing (the condition is analyzed but returns None for dynamic keys).
#[test]
fn narrow_hasattr_dynamic_key_no_narrowing() {
    let nix = r#"x: k: if x ? ${k} then x else null"#;
    let ty = get_inferred_root(nix);
    // Should not crash; just verify it infers a lambda.
    assert!(
        matches!(ty, OutputTy::Lambda { .. }),
        "dynamic hasattr should still produce a lambda, got: {ty}"
    );
}

/// Multi-element attrpath like `x ? a.b` should not crash — narrowing
/// only handles single-key paths and falls back gracefully.
#[test]
fn narrow_hasattr_multi_key_no_narrowing() {
    let nix = "x: if x ? a.b then 1 else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // No narrowing applied, but both branches return int.
    assert_eq!(*body, arc_ty!(Int), "multi-key hasattr body should be int");
}

/// Narrowing + field access with arithmetic: `if x ? count then x.count + 1 else 0`.
/// The field access in the then-branch is narrowed, and arithmetic constrains
/// the result to a numeric type.
#[test]
fn narrow_hasattr_field_access_then_arithmetic() {
    let nix = indoc! {"
        x:
        if x ? count then x.count + 1
        else 0
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    match body {
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        OutputTy::Primitive(PrimitiveTy::Number) => {}
        OutputTy::Union(members) => {
            for m in members {
                assert!(
                    matches!(
                        &*m.0,
                        OutputTy::Primitive(PrimitiveTy::Int)
                            | OutputTy::Primitive(PrimitiveTy::Number)
                            | OutputTy::Primitive(PrimitiveTy::Float)
                    ),
                    "all union members should be numeric, got: {body}"
                );
            }
        }
        _ => panic!("expected numeric body type, got: {body}"),
    }
}

// ==============================================================================
// Type narrowing — type predicate builtins (isString, isInt, etc.)
// ==============================================================================

/// `isString x` — then-branch narrows x to string.
#[test]
fn narrow_isstring_then_is_string() {
    let nix = r#"x: if isString x then builtins.stringLength x else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

#[test]
fn narrow_isstring_then_is_string_ret() {
    let nix = r#"x: if isString x then x else "else case""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// `builtins.isString x` — qualified form should also work.
#[test]
fn narrow_builtins_isstring() {
    let nix = r#"x: if builtins.isString x then builtins.stringLength x else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// Locally aliased builtin: `let isString = builtins.isString; in ...`
/// The narrowing should trace through the local definition to recognize
/// the builtin call. Regression test for nixpkgs patterns like
/// `inherit (builtins) isString`.
#[test]
fn narrow_isstring_local_alias() {
    let nix = r#"
        let isString = builtins.isString;
        in x: if isString x then builtins.stringLength x else 0
    "#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(Int),
        "locally-aliased isString should narrow"
    );
}

/// `inherit (builtins) isString` — same as local alias but via inherit.
#[test]
fn narrow_isstring_inherit_from_builtins() {
    let nix = r#"
        let inherit (builtins) isString;
        in x: if isString x then builtins.stringLength x else 0
    "#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(Int),
        "inherit-from-builtins isString should narrow"
    );
}

/// `isInt x` — then-branch narrows x to int.
#[test]
fn narrow_isint_then_is_int() {
    let nix = "x: if isInt x then x + 1 else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// `isBool x` — then-branch narrows x to bool.
#[test]
fn narrow_isbool_then_is_bool() {
    let nix = "x: if isBool x then !x else false";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Bool), "body should be bool");
}

/// `isFloat x` — then-branch narrows x to float.
#[test]
fn narrow_isfloat_then_is_float() {
    let nix = "x: if isFloat x then x + 1.0 else 0.0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Float), "body should be float");
}

/// `!isString x` — negation flips narrowing.
#[test]
fn narrow_negated_isstring() {
    let nix = r#"x: if !(isString x) then 0 else builtins.stringLength x"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// Else-branch of `isString x` should produce a fresh variable linked to
/// the original. The else-branch can still access fields from the original.
#[test]
fn narrow_isstring_else_preserves_original() {
    // The else-branch's fresh var is linked to the original, so field access
    // should succeed if the original has the field.
    let nix = indoc! {"
        x: if isString x then builtins.stringLength x
        else x.name
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then: int. Else: unconstrained var from field access.
    // The union should contain int (the unconstrained var may simplify away).
    match body {
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Int))),
                "body should contain int, got: {body}"
            );
        }
        _ => panic!("expected int or union containing int, got: {body}"),
    }
}

/// `isString x` then `isInt x` nested — demonstrates narrowing with different
/// predicates doesn't conflict.
#[test]
fn narrow_isstring_then_isint_nested() {
    let nix = indoc! {"
        x: if isString x then builtins.stringLength x
        else if isInt x then x + 1
        else 0
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

// ==============================================================================
// Type narrowing — builtins.hasAttr "field" x
// ==============================================================================

/// `builtins.hasAttr "name" x` — equivalent to `x ? name`.
#[test]
fn narrow_builtins_hasattr() {
    let nix = r#"x: if builtins.hasAttr "name" x then x.name else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then-branch: x.name (unconstrained var). Else-branch: string.
    // The union should contain string.
    match body {
        OutputTy::Primitive(PrimitiveTy::String) => {}
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::String))),
                "body should contain string, got: {body}"
            );
        }
        _ => panic!("expected string or union containing string, got: {body}"),
    }
}

/// `!(builtins.hasAttr "name" x)` — negation flips narrowing.
#[test]
fn narrow_builtins_hasattr_negated() {
    let nix = r#"x: if !(builtins.hasAttr "name" x) then "default" else x.name"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    match body {
        OutputTy::Primitive(PrimitiveTy::String) => {}
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::String))),
                "body should contain string, got: {body}"
            );
        }
        _ => panic!("expected string or union containing string, got: {body}"),
    }
}

// ==============================================================================
// Type narrowing — one-way linking to original variable
// ==============================================================================

/// HasField narrowing preserves original constraints: if x is known to
/// have field `name` from the outer scope, the narrowed variable in the
/// then-branch should also know about it.
#[test]
fn narrow_hasfield_preserves_original_constraints() {
    // x.name in the then-branch succeeds because the narrowed fresh var
    // is linked to the original which is constrained to have `name`.
    let nix = indoc! {"
        f: let x = f 1; in
        if x ? extra then x.name
        else x.name
    "};
    let ty = get_inferred_root(nix);
    // Should succeed without type error — both branches access x.name.
    let _ = unwrap_lambda(&ty);
}

// ==============================================================================
// Negation types — Ty representation and constraint engine
// ==============================================================================

/// OutputTy::Neg displays as `~null`, `~string`, etc.
#[test]
fn neg_display_primitive() {
    assert_eq!(format!("{}", arc_ty!(neg!(Null))), "~null");
    assert_eq!(format!("{}", arc_ty!(neg!(String))), "~string");
    assert_eq!(format!("{}", arc_ty!(neg!(Int))), "~int");
    assert_eq!(format!("{}", arc_ty!(neg!(Bool))), "~bool");
}

/// Compound negation parenthesizes the inner type.
#[test]
fn neg_display_compound() {
    let ty = OutputTy::Neg(lang_ty::TyRef::from(OutputTy::Union(vec![
        lang_ty::TyRef::from(OutputTy::Primitive(PrimitiveTy::Int)),
        lang_ty::TyRef::from(OutputTy::Primitive(PrimitiveTy::String)),
    ])));
    assert_eq!(format!("{ty}"), "~(int | string)");
}

// ==============================================================================
// Negation types — inference output (¬T upper bounds on narrowed variables)
// ==============================================================================

/// Else-branch of a null guard should display `~null` in the output type.
/// Verifies the ¬PrimType upper bound produces visible negation in the
/// canonicalized output. The narrowed var only shows `~null` when it
/// flows into negative position (e.g. as a function argument), since in
/// positive position an unconstrained var is bottom regardless of upper bounds.
#[test]
fn narrow_neg_displayed_in_output() {
    let nix = "f: x: if isNull x then 0 else f x";
    let ty = get_inferred_root(nix);
    let formatted = format!("{ty}");
    // f's parameter type should include ~null because the narrowed x
    // (with ¬Null upper bound) flows into f's param in negative position.
    assert!(
        formatted.contains("~null"),
        "narrowed var flowing to function param should show ~null, got: {formatted}"
    );
}

/// Nested redundant `isString` guards should not error. The inner guard's
/// equality comparison on an already-narrowed variable must not trigger
/// `String <: ¬String`.
#[test]
fn narrow_nested_redundant_isstring() {
    let nix = r#"x: if isString x then (if isString x then builtins.stringLength x else 0) else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// Nested different predicates: outer `!(isNull x)` adds ¬Null, inner
/// `isString x` adds String. Both narrow the same variable without conflict.
#[test]
fn narrow_nested_different_pred() {
    let nix = indoc! {"
        x: if !(isNull x) then (if isString x then builtins.stringLength x else x) else 0
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Then-then: int (stringLength). Then-else: x (narrowed var).
    // Outer else: 0 (int). Body contains int at minimum.
    match body {
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        OutputTy::Union(members) => {
            assert!(
                members
                    .iter()
                    .any(|m| matches!(&*m.0, OutputTy::Primitive(PrimitiveTy::Int))),
                "body should contain int, got: {body}"
            );
        }
        _ => panic!("expected int or union containing int, got: {body}"),
    }
}

// ==============================================================================
// Compound-type narrowing (isAttrs, isList, isFunction)
// ==============================================================================

/// `isAttrs x` narrows x to an attrset in the then-branch, allowing
/// field access on a previously unconstrained variable.
#[test]
fn narrow_isattrs_then_field_access() {
    let nix = r#"x: if isAttrs x then x.name else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// `builtins.isAttrs x` — qualified form.
#[test]
fn narrow_builtins_isattrs() {
    let nix = r#"x: if builtins.isAttrs x then x.name else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// `isAttrs x` then-branch: returning x preserves the attrset constraint.
#[test]
fn narrow_isattrs_then_returns_attrset() {
    let nix = r#"x: if isAttrs x then x else {}"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Both branches produce attrsets, so the result should be an attrset.
    assert!(
        matches!(body, OutputTy::AttrSet(_)),
        "expected attrset, got: {body}"
    );
}

/// `isList x` narrows x to a list in the then-branch.
#[test]
fn narrow_islist_then_head() {
    let nix = r#"x: if isList x then builtins.head x else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Inference succeeds without error: isList narrows x to a list, so
    // `head x` is valid. The body type is int|element — no stronger
    // assertion is possible since the element type is unconstrained.
}

/// `builtins.isList x` — qualified form.
#[test]
fn narrow_builtins_islist() {
    let nix = r#"x: if builtins.isList x then builtins.length x else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "length returns int");
}

/// `isFunction x` narrows x to a function in the then-branch, allowing
/// it to be applied.
#[test]
fn narrow_isfunction_then_apply() {
    let nix = r#"x: if isFunction x then x 42 else 0"#;
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Inference succeeds: isFunction narrows x to a function, so `x 42`
    // is valid. The return type of `x` is unconstrained, so no stronger
    // assertion than "no error" is possible.
}

/// `builtins.isFunction x` — qualified form.
#[test]
fn narrow_builtins_isfunction() {
    let nix = r#"x: if builtins.isFunction x then x "hello" else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Inference succeeds: builtins.isFunction narrows x to a function.
    // The return type of `x "hello"` is unconstrained, so no stronger
    // assertion than "no error" is possible.
}

/// Local alias for isAttrs should be traced through.
#[test]
fn narrow_isattrs_local_alias() {
    let nix = r#"
        let isAttrs = builtins.isAttrs;
        in x: if isAttrs x then x.name else "default"
    "#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

/// `inherit (builtins) isList` alias.
#[test]
fn narrow_islist_inherit_alias() {
    let nix = r#"
        let inherit (builtins) isList;
        in x: if isList x then builtins.length x else 0
    "#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int), "body should be int");
}

/// Negated compound predicate: `!(isAttrs x)` — else-branch should get
/// the attrset narrowing (since then/else are flipped).
#[test]
fn narrow_negated_isattrs() {
    let nix = r#"x: if !(isAttrs x) then "not an attrset" else x.name"#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String), "body should be string");
}

// ==============================================================================
// Uppercase primitive aliases in annotations
// ==============================================================================

// Nixpkgs doc comments use uppercase `String`, `Bool`, etc. These should be
// recognized as the corresponding lowercase primitives, not as unresolved
// type alias references (which would become fresh variables).
test_case!(
    annotation_uppercase_string,
    "
        let
            /** type: f :: String -> String */
            f = x: x;
        in
        f \"hello\"
    ",
    String
);

test_case!(
    annotation_uppercase_int,
    "
        let
            /** type: f :: Int -> Bool */
            f = x: x == 0;
        in
        f 42
    ",
    Bool
);

// Mixed uppercase and lowercase primitives in the same annotation.
test_case!(
    annotation_mixed_case_primitives,
    "
        let
            /** type: f :: String -> int */
            f = x: builtins.stringLength x;
        in
        f \"hello\"
    ",
    Int
);

// ==============================================================================
// Annotation arity mismatch detection
// ==============================================================================

/// When a doc comment annotation has fewer arrows than the function's visible
/// lambda count, we skip the annotation and emit a warning rather than
/// corrupting the type table. Regression test for nameFromURL in strings.nix.
#[test]
fn annotation_arity_mismatch_skipped_with_warning() {
    let nix_src = indoc! { "
        let
            /** type: f :: string -> string */
            f = x: y: x + y;
        in
        f \"hello\" \" world\"
    " };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::default(),
        HashMap::new(),
        HashMap::new(),
    );

    // Inference should succeed (the wrong-arity annotation is skipped).
    let inference = result
        .inference
        .expect("inference should succeed despite arity mismatch");

    // Root should be string (string + string = string).
    let root_ty = inference
        .expr_ty_map
        .get(mod_.entry_expr)
        .expect("root should have a type");
    assert_eq!(
        *root_ty,
        arc_ty!(String),
        "root should be string, got: {root_ty}"
    );

    // Should have a warning diagnostic about the arity mismatch.
    assert!(
        result.diagnostics.iter().any(|d| matches!(
            &d.kind,
            TixDiagnosticKind::AnnotationArityMismatch { name, annotation_arity: 1, expression_arity: 2 }
            if name == "f"
        )),
        "expected AnnotationArityMismatch warning, diagnostics: {:?}",
        result.diagnostics.iter().map(|d| &d.kind).collect::<Vec<_>>()
    );
}

// An annotation with MORE arrows than visible lambdas is allowed (eta-reduction).
// E.g. `escape :: [string] -> string -> string` on `escape = list: replaceStrings ...`
// where the body returns a function.
test_case!(
    annotation_more_arrows_than_lambdas_ok,
    "
        let
            /** type: f :: int -> int -> int */
            f = x: builtins.add x;
        in
        f 1 2
    ",
    Int
);

// ==============================================================================
// Union annotation skip
// ==============================================================================

/// Annotations with union types in parameters are skipped because bidirectional
/// constraints would push all union members as lower bounds into the inferred
/// parameter, causing false errors in branch-specific code. The function should
/// still type-check based on its body.
#[test]
fn annotation_with_union_skipped() {
    let nix_src = indoc! { r#"
        let
            /** type: f :: string -> (string | [string]) -> string */
            f = name: value:
                if builtins.isList value then "list"
                else value;
        in
        f "x" "hello"
    "# };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::default(),
        HashMap::new(),
        HashMap::new(),
    );

    // Inference should succeed — the union annotation is skipped.
    let inference = result
        .inference
        .expect("inference should succeed with union annotation");

    let root_ty = inference
        .expr_ty_map
        .get(mod_.entry_expr)
        .expect("root should have a type");
    // The body returns "list" (string) or value; with the call f "x" "hello",
    // the result should be string.
    assert_eq!(
        *root_ty,
        arc_ty!(String),
        "root should be string, got: {root_ty}"
    );

    // No type errors should be present (warnings are ok).
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| {
            !matches!(
                d.kind,
                TixDiagnosticKind::UnresolvedName { .. }
                    | TixDiagnosticKind::AnnotationArityMismatch { .. }
            )
        })
        .collect();
    assert!(
        errors.is_empty(),
        "no type errors expected, got: {:?}",
        errors.iter().map(|d| &d.kind).collect::<Vec<_>>()
    );
}

// ==============================================================================
// Type narrowing — lib.*.is* select-chain predicates
// ==============================================================================

/// `lib.types.isString x` narrows x to string via leaf-name matching.
#[test]
fn narrow_lib_types_isstring() {
    let nix = indoc! {r#"
        let lib = { types = { isString = builtins.isString; }; };
        in x: if lib.types.isString x then x else "default"
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "lib.types.isString should narrow to string"
    );
}

/// `lib.trivial.isFunction x` narrows x to a function, allowing application.
#[test]
fn narrow_lib_trivial_isfunction() {
    let nix = indoc! {r#"
        let lib = { trivial = { isFunction = builtins.isFunction; }; };
        in x: if lib.trivial.isFunction x then x 42 else 0
    "#};
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Should not error — x is narrowed to a function.
}

/// `lib.isAttrs x` (single-level Select) narrows x to attrset.
#[test]
fn narrow_lib_isattrs() {
    let nix = indoc! {r#"
        let lib = { isAttrs = builtins.isAttrs; };
        in x: if lib.isAttrs x then x.name else "default"
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "lib.isAttrs should narrow to attrset"
    );
}

/// `lib.types.isList x` narrows x to a list.
#[test]
fn narrow_lib_types_islist() {
    let nix = indoc! {r#"
        let lib = { types = { isList = builtins.isList; }; };
        in x: if lib.types.isList x then builtins.length x else 0
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(Int),
        "lib.types.isList should narrow to list"
    );
}

/// `!(lib.types.isString x)` flips narrowing — else-branch gets string.
#[test]
fn narrow_negated_lib_types_isstring() {
    let nix = indoc! {r#"
        let lib = { types = { isString = builtins.isString; }; };
        in x: if !(lib.types.isString x) then "not a string" else x
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "negated lib.types.isString should narrow else to string"
    );
}

// ==============================================================================
// Negation normalization — integration tests
// ==============================================================================

/// Nested contradictory guards: `isString x` then `!isString x` nested.
/// The inner then-branch has x narrowed to `string ∧ ¬string` (⊥), so the
/// body should still type-check without crashing.
#[test]
fn narrow_contradictory_guards_no_crash() {
    let nix = indoc! {r#"
        x: if isString x then
            (if !(isString x) then 42 else 0)
        else "default"
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // The inner else returns 0 (int), the outer else returns "default" (string).
    // The contradictory branch returns 42 (int). Union of int | string.
    match body {
        OutputTy::Union(_) => {}
        OutputTy::Primitive(PrimitiveTy::Int) => {}
        OutputTy::Primitive(PrimitiveTy::String) => {}
        _ => panic!("expected union or primitive, got: {body}"),
    }
}

/// `isString x` then `isInt x` nested — the inner then-branch narrows
/// x to `string ∧ int` which is contradictory (different types). The
/// test verifies inference doesn't crash.
#[test]
fn narrow_contradictory_different_preds_no_crash() {
    let nix = indoc! {"
        x: if isString x then
            (if isInt x then x + 1 else 0)
        else 0
    "};
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Should not crash. The contradictory branch's result doesn't matter
    // much — the key assertion is that inference completes.
}

// ==============================================================================
// Type narrowing — coverage gaps
// ==============================================================================

/// Unrecognized condition — no false narrowing should be applied.
/// A user-defined predicate that happens to return bool shouldn't narrow.
#[test]
fn narrow_unrecognized_condition_no_narrowing() {
    let nix = indoc! {"
        let check = _: true; in x: if check x then x else x
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert!(
        matches!(body, OutputTy::TyVar(_)),
        "unrecognized predicate should not narrow — body should be TyVar, got: {body}"
    );
}

/// Narrowing inside a let body should not break let-generalization.
/// `f` should be polymorphic — the narrowing in the body should be local.
#[test]
fn narrow_let_generalization_preserved() {
    let nix = indoc! {"
        let f = x: if x == null then \"default\" else x; in f
    "};
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // The key assertion is that `f` is inferred as a function type.
    // If narrowing broke generalization, this would fail or produce a
    // monomorphic type instead of a polymorphic one.
}

/// Known limitation: negation bounds are lost through let-generalization.
/// When `f = x: if isNull x then 0 else x` is generalized, the ¬null
/// upper bound on x's narrowed var doesn't survive extrude. The output
/// is `a -> int` (union of `0 | x` collapses to `int` for the then-branch
/// and the else-branch's x loses its negation information).
///
/// Contrast with `narrow_neg_displayed_in_output` which uses a curried
/// lambda (`f: x: ...`) where f's param is in negative position and
/// the ¬null bound is visible without generalization.
// TODO: preserve negation bounds through extrude so `let f = x: ...`
// retains `~null` in f's type after generalization.
#[test]
fn narrow_neg_lost_through_generalization() {
    let nix = indoc! {"
        let f = x: if builtins.isNull x then 0 else x; in f
    "};
    let ty = get_inferred_root(nix);
    let formatted = ty.to_string();
    // Currently, negation is lost — output is `a -> int` instead of
    // `(a & ~null) -> int`. This test documents the current behavior.
    assert!(
        !formatted.contains("~null"),
        "documenting current behavior: negation should be lost through generalization, got: {formatted}"
    );
}

/// Type error quality under narrowing: then-branch narrows x to null,
/// but `stringLength` expects string → should produce TypeMismatch.
#[test]
fn narrow_type_error_in_narrowed_branch() {
    let nix = indoc! {"
        x: if builtins.isNull x then builtins.stringLength x else 0
    "};
    let error = get_check_error(nix);
    assert!(
        matches!(error, TixDiagnosticKind::TypeMismatch { .. }),
        "narrowed branch type error should be TypeMismatch, got: {error:?}"
    );
}

/// Select-chain heuristic: `myModule.isString x` narrows because the
/// leaf name matches `isString`. This documents the intentional heuristic
/// that activates narrowing based on naming convention.
#[test]
fn narrow_select_chain_heuristic_activates() {
    let nix = indoc! {"
        let myModule = { isString = _: true; }; in
        x: if myModule.isString x then builtins.stringLength x else 0
    "};
    // Narrowing activates: then-branch sees x as string, stringLength
    // succeeds, else-branch returns int. Body is int.
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        OutputTy::Primitive(PrimitiveTy::Int),
        "select-chain heuristic should narrow — body should be int, got: {body}"
    );
}

/// Non-predicate select-chain leaf — no narrowing should be applied.
/// A leaf name like `checkValue` doesn't match any known predicate.
#[test]
fn narrow_select_chain_non_predicate_no_narrowing() {
    let nix = indoc! {"
        let myModule = { checkValue = _: true; }; in
        x: if myModule.checkValue x then x else x
    "};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert!(
        matches!(body, OutputTy::TyVar(_)),
        "non-predicate leaf should not narrow — body should be TyVar, got: {body}"
    );
}

// ==============================================================================
// Type narrowing — conditional library functions
// ==============================================================================
//
// Functions like lib.optionalString, lib.optionalAttrs, lib.optional, and
// lib.mkIf take a boolean guard as their first argument and only evaluate
// the second argument when the guard is true. The checker detects these by
// name and applies then-branch narrowing to the body argument.

/// `lib.optionalString (x != null) x.name` — the body (x.name) should be
/// inferred under narrowing from the null guard. Without narrowing, x.name
/// would produce a false error because x might be null.
/// Uses stubs so the function signature constrains the return type to string.
#[test]
fn narrow_optional_string_null_guard() {
    let registry =
        registry_from_tix("module lib { val optionalString :: bool -> string -> string; }");
    let nix = indoc! {r#"
        let
            /** type: lib :: Lib */
            lib = { optionalString = cond: str: if cond then str else ""; };
        in x: lib.optionalString (x != null) x.name
    "#};
    let ty = get_inferred_root_with_aliases(nix, &registry);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "optionalString with null guard should return string"
    );
}

/// `lib.optionalAttrs (x != null) { inherit (x) name; }` — the body attrset
/// is inferred under narrowing. The inherit from x succeeds because x is
/// narrowed to non-null.
#[test]
fn narrow_optional_attrs_null_guard() {
    let nix = indoc! {r#"
        let lib = { optionalAttrs = cond: attrs: if cond then attrs else {}; };
        in x: lib.optionalAttrs (x != null) { y = x.name; }
    "#};
    // Should not error — x.name in the body is under null-guard narrowing.
    // optionalAttrs returns {} or {y = ...}, so result is an attrset.
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert!(
        matches!(body, OutputTy::AttrSet(_)),
        "optionalAttrs should return attrset, got: {body}"
    );
}

/// `lib.optional (x != null) x.field` — body is narrowed, returns a list.
#[test]
fn narrow_optional_null_guard() {
    let nix = indoc! {r#"
        let lib = { optional = cond: val: if cond then [val] else []; };
        in x: lib.optional (x != null) x.field
    "#};
    // Should not error — x.field is under null-guard narrowing.
    // optional returns [val] | [], which canonicalizes as a union of
    // two list types. Verify the body contains list structure.
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    let body_str = body.to_string();
    assert!(
        body_str.contains('['),
        "optional should return list-shaped type, got: {body}"
    );
}

/// `lib.mkIf (x != null) x.name` — mkIf is a conditional function too.
#[test]
fn narrow_mkif_null_guard() {
    let nix = indoc! {r#"
        let lib = { mkIf = cond: val: if cond then { value = val; } else {}; };
        in x: lib.mkIf (x != null) x.name
    "#};
    // Should not error — x.name is under null-guard narrowing.
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
}

/// `lib.optionalString true "hello"` — no narrowing condition (true is not
/// a recognized guard pattern), but the call should still work normally.
#[test]
fn narrow_optional_string_no_guard() {
    let nix = indoc! {r#"
        let lib = { optionalString = cond: str: if cond then str else ""; };
        in lib.optionalString true "hello"
    "#};
    let ty = get_inferred_root(nix);
    assert_eq!(
        ty,
        arc_ty!(String),
        "optionalString true \"hello\" should be string"
    );
}

/// `lib.strings.optionalString (x != null) x.name` — nested module path
/// should also be detected (leaf name is still "optionalString").
/// Uses stubs for the function signature.
#[test]
fn narrow_optional_string_nested_select() {
    let registry = registry_from_tix(indoc! {"
        module lib {
            module strings {
                val optionalString :: bool -> string -> string;
            }
        }
    "});
    let nix = indoc! {r#"
        let
            /** type: lib :: Lib */
            lib = { strings = { optionalString = cond: str: if cond then str else ""; }; };
        in x: lib.strings.optionalString (x != null) x.name
    "#};
    let ty = get_inferred_root_with_aliases(nix, &registry);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "lib.strings.optionalString with null guard should return string"
    );
}

/// Bare `optionalString` reference (from `with lib;` or local binding)
/// should also be detected as a conditional function.
/// Uses a global val stub so the bare name resolves with the right type.
#[test]
fn narrow_optional_string_bare_reference() {
    let registry = registry_from_tix("val optionalString :: bool -> string -> string;");
    let nix = "x: optionalString (x != null) x.name";
    let ty = get_inferred_root_with_aliases(nix, &registry);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "bare optionalString with null guard should return string"
    );
}

/// `lib.optionalString (isString x) (x + " suffix")` — isString guard
/// narrows x to string, so string concatenation succeeds.
#[test]
fn narrow_optional_string_isstring_guard() {
    let nix = indoc! {r#"
        let lib = { optionalString = cond: str: if cond then str else ""; };
        in x: lib.optionalString (builtins.isString x) (x + " suffix")
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "optionalString with isString guard should return string"
    );
}

// ==============================================================================
// Intersection-of-lambda annotation handling
// ==============================================================================

/// An intersection-of-lambda annotation should not produce a type error.
/// The body is type-checked via normal inference; the annotation is stored
/// for callers without bidirectional constraints.
#[test]
fn intersection_annotation_accepted() {
    let nix_src = indoc! { "
        let
            /** type: dispatch :: (int -> int) & (string -> string) */
            dispatch = x:
                if builtins.isInt x then x + 1
                else x;
        in
        dispatch 42
    " };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::default(),
        HashMap::new(),
        HashMap::new(),
    );

    // Inference should succeed — the intersection annotation is accepted.
    let inference = result
        .inference
        .expect("inference should succeed with intersection annotation");

    let root_ty = inference
        .expr_ty_map
        .get(mod_.entry_expr)
        .expect("root should have a type");
    // The call `dispatch 42` infers from the body: isInt narrows to int,
    // x + 1 produces int.
    assert_eq!(*root_ty, arc_ty!(Int), "root should be int, got: {root_ty}");
}

/// The AnnotationUnchecked warning should be emitted for intersection-of-lambda
/// annotations.
#[test]
fn intersection_annotation_warning_emitted() {
    let nix_src = indoc! { "
        let
            /** type: f :: (int -> int) & (string -> string) */
            f = x: x;
        in
        f 1
    " };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let _mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::default(),
        HashMap::new(),
        HashMap::new(),
    );

    result.inference.expect("inference should succeed");

    assert!(
        result.diagnostics.iter().any(|d| matches!(
            &d.kind,
            TixDiagnosticKind::AnnotationUnchecked { name, .. }
            if name == "f"
        )),
        "expected AnnotationUnchecked warning, diagnostics: {:?}",
        result
            .diagnostics
            .iter()
            .map(|d| &d.kind)
            .collect::<Vec<_>>()
    );
}

/// An intersection of non-lambda types (e.g. `int & string`) should NOT
/// trigger the intersection-of-lambda guard; it falls through to the
/// normal intern + constrain path.
#[test]
fn non_lambda_intersection_falls_through() {
    // `int & string` as an annotation is contradictory — it should
    // either error or produce a constrained type, not be silently
    // skipped via the intersection-of-lambda path.
    let nix_src = indoc! { "
        let
            /** type: x :: int & string */
            x = 42;
        in
        x
    " };
    let (db, file) = TestDatabase::single_file(nix_src).unwrap();
    let _mod_ = module(&db, file);
    let result = crate::check_file_collecting(
        &db,
        file,
        &TypeAliasRegistry::default(),
        HashMap::new(),
        HashMap::new(),
    );

    // The intersection-of-lambda guard should NOT have fired, so there
    // should be no AnnotationUnchecked warning.
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| matches!(&d.kind, TixDiagnosticKind::AnnotationUnchecked { .. })),
        "non-lambda intersection should not produce AnnotationUnchecked, diagnostics: {:?}",
        result
            .diagnostics
            .iter()
            .map(|d| &d.kind)
            .collect::<Vec<_>>()
    );
}

// ==============================================================================
// Type narrowing — let-bindings under narrowing scopes (SCC pre-pass)
// ==============================================================================
//
// When a let-binding is inside a narrowing scope (if-then-else branch, assert
// body, conditional function argument), the SCC group processing must install
// narrowing overrides so that references to narrowed names get the narrowed
// type. Without this, the binding is inferred before the if-then-else installs
// overrides, causing false type errors.

/// Regression: `{ x ? null }: if x != null then (let y = x.name; in y) else ""`
/// The let-binding `y = x.name` is inside the then-branch of a null guard.
/// Without the SCC narrowing pre-pass, x.name would see the un-narrowed x
/// (which includes null from the default), producing a false type error.
#[test]
fn narrow_let_binding_under_null_guard() {
    let nix = indoc! {r#"
        { x ? null }: if x != null then (let y = x.name; in y) else ""
    "#};
    let ty = get_inferred_root(nix);
    // Should succeed without error — x is narrowed to non-null in the let.
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(
        *body,
        arc_ty!(String),
        "let binding under null guard should succeed, got: {body}"
    );
}

/// Assert narrowing with let-binding: `x: assert x != null; let y = x.name; in y`
/// The assert narrows x to non-null, so y = x.name should succeed.
#[test]
fn narrow_assert_then_let_binding() {
    let nix = "x: assert x != null; let y = x.name; in y";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert!(
        matches!(body, OutputTy::TyVar(_)),
        "assert-narrowed let binding body should be a type variable (from field access), got: {body}"
    );
}

/// Nested narrowing with let-bindings: inner if narrows further, and the
/// let-binding inside the inner then-branch should see both narrowings.
#[test]
fn narrow_nested_let_bindings() {
    let nix = indoc! {r#"
        x: if x != null then
            (if x ? name then
                (let y = x.name; in y)
            else "no name")
        else "null"
    "#};
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    // Should succeed: x is narrowed to non-null and has `name` field.
    assert_eq!(
        *body,
        arc_ty!(String),
        "nested narrowing with let binding should succeed, got: {body}"
    );
}

/// Multiple let-bindings in the same let under one guard.
/// Both y and z access fields of the narrowed x.
#[test]
fn narrow_multiple_let_bindings_under_guard() {
    let nix = indoc! {"
        x: if x != null then
            (let
                y = x.name;
                z = x.value;
            in { inherit y z; })
        else {}
    "};
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // Should succeed without error — both y and z see narrowed x.
}

/// Conditional library function with let-binding inside the body argument.
/// `lib.optionalString (x != null) (let y = x.name; in y)` — the body arg
/// is only evaluated when the guard is true, so x.name should succeed.
/// Without the SCC narrowing pre-pass, this would produce a false type error
/// because y = x.name would see un-narrowed x (which includes null).
#[test]
fn narrow_conditional_fn_let_binding() {
    let nix = indoc! {r#"
        x: let lib = { optionalString = cond: str: if cond then str else ""; };
        in lib.optionalString (x != null) (let y = x.name; in y)
    "#};
    let ty = get_inferred_root(nix);
    let (_param, _body) = unwrap_lambda(&ty);
    // The key assertion is that inference succeeds without a type error.
    // The let-bound y = x.name sees narrowed x (non-null) via the pre-pass.
}

// ==============================================================================
// Type narrowing + overload interaction tests (G2)
// ==============================================================================
//
// These tests verify that type narrowing and operator overload resolution
// compose correctly: narrowing a variable to a concrete type in a branch
// should let the overloaded `+` operator resolve to the correct result type.

/// `x: if isInt x then x + 1 else 0` — isInt narrows x to int in the
/// then-branch, so `+` resolves to int addition. Body is int.
#[test]
fn narrow_isint_then_add() {
    let nix = "x: if builtins.isInt x then x + 1 else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}

/// `x: if isNull x then 0 else x + 1` — else-branch has x narrowed to
/// ~null, and `+ 1` constrains x to Number. Body is int.
#[test]
fn narrow_isnull_else_add() {
    let nix = "x: if builtins.isNull x then 0 else x + 1";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}

/// `x: y: if isInt x then (if isInt y then x + y else 0) else 0`
/// — both x and y are narrowed to int, so `x + y` resolves to int.
#[test]
fn narrow_isint_nested_arithmetic() {
    let nix = "x: y: if builtins.isInt x then (if builtins.isInt y then x + y else 0) else 0";
    let ty = get_inferred_root(nix);
    let (_param, inner) = unwrap_lambda(&ty);
    let (_param2, body) = unwrap_lambda(inner);
    assert_eq!(*body, arc_ty!(Int));
}

/// `x: if isString x then x + "suffix" else "default"` — isString narrows
/// x to string, so `+` resolves to string concatenation. Body is string.
#[test]
fn narrow_isstring_then_concat() {
    let nix = r#"x: if builtins.isString x then x + "suffix" else "default""#;
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(String));
}

/// `x: if x ? count then x.count + 1 else 0` — `? count` narrows x to
/// have a `count` field, field access succeeds, and `+ 1` resolves to int.
#[test]
fn narrow_hasattr_field_arithmetic() {
    let nix = "x: if x ? count then x.count + 1 else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}

// ==============================================================================
// Negation + intersection contradiction tests (G3)
// ==============================================================================
//
// These tests document behavior when narrowing produces contradictory types
// (e.g. `string & int`, `float & ~float`). Contradictions currently resolve
// to TyVar stand-ins; after A2 (OutputTy::Bottom) they will resolve to `never`.

/// `x: if isString x then (if isInt x then x else 0) else 0` — the inner
/// then-branch has `string & int` which is contradictory. The overall
/// body is int (both non-contradictory branches return int).
#[test]
fn narrow_contradiction_isstring_then_isint() {
    let nix = "x: if builtins.isString x then (if builtins.isInt x then x else 0) else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}

/// `x: if !(isNull x) then (if isString x then stringLength x else 0) else 0`
/// — `~null & string` is NOT contradictory. The body is int (stringLength
/// returns int, else branches return int).
#[test]
fn narrow_non_contradiction_neg_null_string() {
    let nix = "x: if !(builtins.isNull x) then (if builtins.isString x then builtins.stringLength x else 0) else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}

/// `x: if isFloat x then (if !(isFloat x) then x else 0) else 0` —
/// `float & ~float` is a contradiction. Body is int.
#[test]
fn narrow_contradiction_self_negated() {
    let nix = "x: if builtins.isFloat x then (if !(builtins.isFloat x) then x else 0) else 0";
    let ty = get_inferred_root(nix);
    let (_param, body) = unwrap_lambda(&ty);
    assert_eq!(*body, arc_ty!(Int));
}
