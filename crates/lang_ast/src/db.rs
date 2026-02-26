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
    /// RootDatabase caches the parse result so repeated calls for the same
    /// file don't re-parse. The cache is cleared when file contents change.
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root>;

    /// Load a file from disk by path. Returns None if the file doesn't exist
    /// or can't be read. Used by multi-file import resolution.
    fn load_file(&self, path: &std::path::Path) -> Option<NixFile>;
}

#[derive(Default, Clone)]
#[salsa::db]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, NixFile>,
    /// Cache parse results to avoid re-parsing when `parse_file` is called
    /// multiple times for the same file (e.g. once from `module_and_source_maps`
    /// and once to store in `SyntaxData`). Cleared by `set_file_contents`.
    parse_cache: DashMap<NixFile, rnix::Parse<rnix::Root>>,
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl AstDb for RootDatabase {
    fn parse_file(&self, file: NixFile) -> rnix::Parse<rnix::Root> {
        if let Some(cached) = self.parse_cache.get(&file) {
            return cached.clone();
        }
        let src = file.contents(self);
        let parsed = rnix::Root::parse(src);
        self.parse_cache.insert(file, parsed.clone());
        parsed
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
            // Invalidate cached parse — contents are changing.
            self.parse_cache.remove(&file);
            file.set_contents(self).to(contents);
            file
        } else {
            let file = NixFile::new(self, path.clone(), contents);
            self.files.insert(path, file);
            file
        }
    }
}
