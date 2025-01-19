use std::path::PathBuf;

use rnix::Root;
use salsa::Event;

use crate::{Db, db::NixFile};

const DEFAULT_IMPORT_FILE: &str = "default.nix";

#[derive(Default, Clone)]
#[salsa::db]
pub struct TestDatabase {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for TestDatabase {
    fn salsa_event(&self, _event: &dyn Fn() -> Event) {}
}

#[salsa::db]
impl Db for TestDatabase {
    fn parse_file(&self, file: NixFile) -> Root {
        let src = file.contents(self);
        rnix::Root::parse(src).tree()
    }
}

#[salsa::tracked]
impl TestDatabase {
    pub fn single_file(fixture: &str) -> miette::Result<(Self, NixFile)> {
        let db = Self::default();

        let path: PathBuf = format!("/{DEFAULT_IMPORT_FILE}").into();

        let file = NixFile::new(&db, path, fixture.into());

        Ok((db, file))
    }
}

// #[derive(Default, Debug)]
// pub struct Fixture {
//     files: Vec<NixFile>,
// }

// impl Fixture {
//     pub fn new(fixture: &str) -> miette::Result<Self> {
//         let mut this = Self::default();

//         // TODO: parse the fixture to allow for multiple "files" in one string

//         let path: PathBuf = format!("/{DEFAULT_IMPORT_FILE}").into();

//         Ok(this)
//     }
// }
