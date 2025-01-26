use indoc::indoc;

use super::check_file;
use crate::{arc_ty, tests::TestDatabase, ty::ArcTy};

#[track_caller]
fn check(src: &str, expected: ArcTy) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = crate::module(&db, file);
    let inference = check_file(&db, file).expect("No inference error");

    let root_ty = inference
        .expr_ty_map
        .get(&module.entry_expr)
        .expect("No type for root module entry");

    assert_eq!(root_ty, &expected)
}

macro_rules! test_case {
    ($name:ident, $file:tt, $ty:tt) => {
        #[test]
        fn $name() {
            let file = indoc! { $file };
            let ty = arc_ty!($ty);
            check(file, ty);
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
        # TODO: overloading needs to handle the case when one of the know types is a type var
        # add = a: b: a + b;
        lst = [(1) (2)];
    }
    ", 
    {
    "num": (Int),
    "str": (String),
    "bool": (Bool),
    "null": (Null),
    "float": (Float),
    // "add": (Int -> Int -> Int),
    "lst": [Int]
    }
);

test_case!(equality, "1 == 0", Bool);

test_case!(basic_merge, "
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
    let id = (a: a); in
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
