use std::path::PathBuf;

use dashmap::DashMap;
use salsa::{self, Setter};

#[salsa::input]
pub struct NixFile {
    pub path: PathBuf,
    #[returns(ref)]
    pub contents: String,
}

#[salsa::db]
pub trait AstDb: salsa::Database {
    /// Parse a Nix file, returning the `Parse<Root>` which stores the green
    /// tree (Send+Sync). Callers get a Root via `.tree()` locally.
    ///
    /// Implementations must always read `file.contents(self)` so that Salsa
    /// records the dependency when this is called from tracked functions
    /// like `module_and_source_maps`.
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root>;

    /// Load a file from disk by path. Returns None if the file doesn't exist
    /// or can't be read. Used by multi-file import resolution.
    fn load_file(&self, path: &std::path::Path) -> Option<NixFile>;
}

#[derive(Clone, Default)]
#[salsa::db]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, NixFile>,
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl AstDb for RootDatabase {
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root> {
        // Must always read file.contents(self) so Salsa records the dependency
        // when called from inside #[salsa::tracked] functions like
        // module_and_source_maps. A manual cache here would bypass the read
        // and break Salsa's invalidation tracking.
        let src = file.contents(self);
        rnix::Root::parse(src)
    }

    fn load_file(&self, path: &std::path::Path) -> Option<NixFile> {
        self.read_file(path.to_path_buf()).ok()
    }
}

#[salsa::tracked]
impl RootDatabase {
    pub fn read_file(&self, path: PathBuf) -> Result<NixFile, std::io::Error> {
        let path = path.canonicalize()?;

        let file = match self.files.entry(path.clone()) {
            dashmap::Entry::Occupied(entry) => *entry.get(),
            dashmap::Entry::Vacant(entry) => {
                let contents = std::fs::read_to_string(&path)?;
                *entry.insert(NixFile::new(self, path, contents))
            }
        };

        Ok(file)
    }
}

impl RootDatabase {
    /// Create or update a NixFile from editor-provided contents (for LSP).
    /// Uses Salsa input mutation to invalidate downstream queries.
    pub fn set_file_contents(&mut self, path: PathBuf, contents: String) -> NixFile {
        // Check if we already have this file — copy the NixFile handle out
        // before releasing the DashMap borrow so we can mutate self.
        let existing = self.files.get(&path).map(|entry| *entry.value());

        if let Some(file) = existing {
            file.set_contents(self).to(contents);
            file
        } else {
            let file = NixFile::new(self, path.clone(), contents);
            self.files.insert(path, file);
            file
        }
    }
}
