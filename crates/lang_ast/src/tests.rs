use std::collections::HashMap;
use std::path::PathBuf;

use crate::{db::NixFile, AstDb};
use rnix::Root;

const DEFAULT_IMPORT_FILE: &str = "default.nix";

#[derive(Default, Clone)]
#[salsa::db]
pub struct TestDatabase {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for TestDatabase {}

#[salsa::db]
impl AstDb for TestDatabase {
    fn parse_file(&self, file: NixFile) -> Root {
        let src = file.contents(self);
        rnix::Root::parse(src).tree()
    }

    fn load_file(&self, _path: &std::path::Path) -> Option<NixFile> {
        // Single-file test database doesn't support imports.
        None
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

// ==============================================================================
// Multi-file test database
// ==============================================================================

/// A test database that supports loading multiple files, enabling multi-file
/// import tests. Files are provided as (path, contents) pairs; `load_file`
/// looks up the path in the pre-loaded map.
#[derive(Clone)]
#[salsa::db]
pub struct MultiFileTestDatabase {
    storage: salsa::Storage<Self>,
    files: HashMap<PathBuf, NixFile>,
}

#[salsa::db]
impl salsa::Database for MultiFileTestDatabase {}

#[salsa::db]
impl AstDb for MultiFileTestDatabase {
    fn parse_file(&self, file: NixFile) -> Root {
        let src = file.contents(self);
        rnix::Root::parse(src).tree()
    }

    fn load_file(&self, path: &std::path::Path) -> Option<NixFile> {
        self.files.get(path).copied()
    }
}

impl MultiFileTestDatabase {
    /// Create a multi-file test database from a list of (path, source) pairs.
    /// The first file is treated as the entry point.
    ///
    /// Paths should be absolute (e.g. "/main.nix", "/lib.nix") so that
    /// import resolution works correctly.
    pub fn new(sources: &[(&str, &str)]) -> (Self, NixFile) {
        let mut db = Self {
            storage: Default::default(),
            files: HashMap::new(),
        };

        let mut entry_file = None;

        for (i, &(path_str, contents)) in sources.iter().enumerate() {
            let path: PathBuf = path_str.into();
            let file = NixFile::new(&db, path.clone(), contents.into());
            db.files.insert(path, file);
            if i == 0 {
                entry_file = Some(file);
            }
        }

        (db, entry_file.expect("at least one file required"))
    }
}
