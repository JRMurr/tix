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

#[test]
fn simple_types() {
    let file = indoc! {"{
        num = 1;
        str = \"foo\";
        bool = true;
        null = null;
        float = 3.14;
        # TODO: overloading needs to handle the case when one of the know types is a type var
        # add = a: b: a + b;
        lst = [(1) (2)];
    }
    "};

    let ty = arc_ty!({
        "num": (Int),
        "str": (String),
        "bool": (Bool),
        "null": (Null),
        "float": (Float),
        // "add": (Int -> Int -> Int),
        "lst": [Int]
    });

    check(file, dbg!(ty));
}

#[test]
fn equality() {
    let file = indoc! {"
        1 == 0
    "};

    let ty = arc_ty! { Bool };

    check(file, dbg!(ty));
}

#[test]
fn basic_merge() {
    let file = indoc! {"
        {
            a = 1;
            b = 2;
        }
        // {
            a = \"hi\";
            c = ./merge.nix;
        }
    "};
    let ty = arc_ty!({
        "a": (String),
        "b": (Int),
        "c": (Path)
    });

    check(file, dbg!(ty));
}

#[test]
fn simple_func() {
    let file = indoc! {"
        (a: b: a + b) 1 2;
    "};
    let ty = arc_ty!(Int);

    check(file, dbg!(ty));
}

#[test]
fn simple_let_gen() {
    let file = indoc! {"
        let id = (a: a); in
        id 1
    "};
    let ty = arc_ty!(Int);

    check(file, dbg!(ty));
}

#[test]
fn simple_let_gen_overload() {
    let file = indoc! {"
        let 
            add = a: b: a + b;
        in
        {
            int = add 1 2;
            float = add 3.14 2;
            str = add \"hi\" ./test.nix;
        }
    "};
    let ty = arc_ty!({
        "int": (Int),
        "float": (Float),
        "str": (String)
    });

    check(file, dbg!(ty));
}
