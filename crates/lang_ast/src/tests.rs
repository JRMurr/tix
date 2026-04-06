use std::collections::HashMap;
use std::path::PathBuf;

use crate::{db::NixFile, AstDb, ExprId, NameId};

const DEFAULT_IMPORT_FILE: &str = "default.nix";

// ==============================================================================
// Shared test helpers
// ==============================================================================

/// Find a NameId by its text. Panics if not found.
pub fn find_name(module: &crate::Module, text: &str) -> NameId {
    module
        .names()
        .find(|(_, n)| n.text == text)
        .unwrap_or_else(|| panic!("name {text:?} not found"))
        .0
}

/// Find the ExprId of the first `Expr::Reference` whose name string
/// matches `text`.
pub fn find_ref_expr(module: &crate::Module, text: &str) -> ExprId {
    module
        .exprs()
        .find(|(_, e)| matches!(e, crate::Expr::Reference(n) if n == text))
        .unwrap_or_else(|| panic!("reference to {text:?} not found"))
        .0
}

/// Find the first `IfThenElse` expression and return its condition ExprId.
pub fn find_if_condition(module: &crate::Module) -> ExprId {
    module
        .exprs()
        .find_map(|(_, e)| match e {
            crate::Expr::IfThenElse { cond, .. } => Some(*cond),
            _ => None,
        })
        .expect("no if-then-else found in module")
}

/// Find the first `Apply` expression and return its ExprId.
pub fn find_apply(module: &crate::Module) -> ExprId {
    module
        .exprs()
        .find_map(|(id, e)| match e {
            crate::Expr::Apply { .. } => Some(id),
            _ => None,
        })
        .expect("no Apply found in module")
}

#[derive(Clone)]
#[salsa::db]
pub struct TestDatabase {
    storage: salsa::Storage<Self>,
}

impl Default for TestDatabase {
    fn default() -> Self {
        Self {
            storage: Default::default(),
        }
    }
}

#[salsa::db]
impl salsa::Database for TestDatabase {}

#[salsa::db]
impl AstDb for TestDatabase {
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root> {
        let src = file.contents(self);
        rnix::Root::parse(src)
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
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root> {
        let src = file.contents(self);
        rnix::Root::parse(src)
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
