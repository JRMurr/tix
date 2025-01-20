use indoc::indoc;

use super::check_file;
use crate::{arc_ty, tests::TestDatabase, ty::ArcTy};

#[track_caller]
fn check(src: &str, expected: ArcTy) {
    let (db, file) = TestDatabase::single_file(src).unwrap();
    let module = crate::module(&db, file);
    let inference = check_file(&db, file);

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
        add = a: b: a + b;
        lst = [(1) (2)];
    }
    "};

    let ty = arc_ty!({
        "num": (Int),
        "str": (String),
        "bool": (Bool),
        "null": (Null),
        "float": (Float),
        "add": (Int -> Int -> Int),
        "lst": [Int]
    });

    check(file, dbg!(ty));
}
