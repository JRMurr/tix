use indoc::indoc;
use lang_ast::{module, tests::TestDatabase, Module};
use lang_ty::{arc_ty, ArcTy, PrimitiveTy};

use crate::{InferenceError, InferenceResult};

use super::check_file;

pub fn check_str(src: &str) -> (Module, Result<InferenceResult, InferenceError>) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = module(&db, file);
    (module, check_file(&db, file))
}

pub fn get_inferred_root(src: &str) -> ArcTy {
    let (module, inference) = check_str(src);

    let inference = inference.expect("No type error");

    inference
        .expr_ty_map
        .get(&module.entry_expr)
        .expect("No type for root module entry")
        .clone()
}

pub fn get_check_error(src: &str) -> InferenceError {
    let (_, inference) = check_str(src);

    inference.expect_err("Expected an inference error")
}

#[track_caller]
pub fn expect_ty_inference(src: &str, expected: ArcTy) {
    let root_ty = get_inferred_root(src);

    assert_eq!(root_ty, expected)
}

#[track_caller]
pub fn expect_inference_error(src: &str, expected: InferenceError) {
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

#[test]
fn type_annotation_mis_match() {
    let file = indoc! { "
        let
            /**
                type: foo :: string
            */
            foo = 1;
        in
        foo
    " };

    // With subtyping, this is a type mismatch between string and int.
    let string_ty = PrimitiveTy::String.into();
    let int_ty = PrimitiveTy::Int.into();

    expect_inference_error(file, InferenceError::TypeMismatch(int_ty, string_ty))
}

/// Look up the type of a named binding by its text name.
/// When the same name has multiple NameIds (e.g. definition + inherit reference),
/// prefer the version without unions/intersections (the clean early-canonicalized form).
fn get_name_type(src: &str, name: &str) -> ArcTy {
    let (module, inference) = check_str(src);
    let inference = inference.expect("No type error");

    let mut best: Option<ArcTy> = None;
    for (name_id, name_data) in module.names() {
        if name_data.text == name {
            if let Some(ty) = inference.name_ty_map.get(&name_id) {
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

    // `addTwo` and `strApply` should be polymorphic (a -> b).
    let add_two_ty = get_name_type(file, "addTwo");
    assert_eq!(add_two_ty, arc_ty!((# 0) -> (# 1)));

    let str_apply_ty = get_name_type(file, "strApply");
    assert_eq!(str_apply_ty, arc_ty!((# 0) -> (# 1)));
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
