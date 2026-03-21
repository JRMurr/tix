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
    /// Insert a pre-read file into the database without any disk I/O.
    ///
    /// The `path` must already be canonicalized. If the file is already loaded
    /// (e.g. from a prior `read_file` call), the existing NixFile is returned.
    /// Used by `tix check` to front-load all file reads in parallel before
    /// the sequential Salsa query loop.
    pub fn preload_file(&self, path: PathBuf, contents: String) -> NixFile {
        match self.files.entry(path.clone()) {
            dashmap::Entry::Occupied(entry) => *entry.get(),
            dashmap::Entry::Vacant(entry) => *entry.insert(NixFile::new(self, path, contents)),
        }
    }

    /// Create or update a NixFile from editor-provided contents (for LSP).
    /// Uses Salsa input mutation to invalidate downstream queries.
    pub fn set_file_contents(&mut self, path: PathBuf, contents: String) -> NixFile {
        // Check if we already have this file — copy the NixFile handle out
        // before releasing the DashMap borrow so we can mutate self.
        let existing = self.files.get(&path).map(|entry| *entry.value());

        if let Some(file) = existing {
            // Skip Salsa mutation if contents haven't changed — avoids an
            // unnecessary revision bump and the downstream query revalidation
            // walk that would follow.
            if *file.contents(&*self) == contents {
                return file;
            }
            file.set_contents(self).to(contents);
            file
        } else {
            let file = NixFile::new(self, path.clone(), contents);
            // Path never changes after creation — mark HIGH so Salsa can skip
            // revalidation of path-dependent queries when only contents change.
            file.set_path(self)
                .with_durability(salsa::Durability::HIGH)
                .to(path.clone());
            self.files.insert(path, file);
            file
        }
    }
}
