use std::path::PathBuf;

use dashmap::DashMap;
use salsa::{self, Setter};

#[salsa::input]
pub struct NixFile {
    pub path: PathBuf,
    #[returns(ref)]
    pub contents: String,
}

/// Stub configuration for type alias loading. Created by the LSP/CLI before
/// analysis begins. Salsa tracks field access, so changes to stub paths
/// automatically invalidate downstream results (e.g. the TypeAliasRegistry
/// and all file_root_type computations).
///
/// Lives in `lang_ast` (not `lang_check`) because it only contains paths and
/// flags — no dependency on check-time types. This avoids circular crate deps.
#[salsa::input]
pub struct StubConfig {
    /// Paths to .tix stub files or directories.
    #[returns(ref)]
    pub stub_paths: Vec<PathBuf>,

    /// Override directory for built-in context stubs (e.g. @nixos, @home-manager).
    #[returns(ref)]
    pub builtin_stubs_dir: Option<PathBuf>,

    /// Whether to include built-in nixpkgs stubs (TypeAliasRegistry::with_builtins).
    pub use_builtins: bool,
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

    /// Retrieve the Salsa-managed stub configuration. Returns `None` until
    /// the LSP or CLI sets it via `RootDatabase::set_stub_config()`.
    fn stub_config(&self) -> Option<StubConfig>;
}

#[derive(Default, Clone)]
#[salsa::db]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, NixFile>,
    /// Salsa input for stub configuration. Created by the LSP/CLI at startup.
    /// Just a Copy integer ID internally — no cross-crate type dependency.
    stub_config: Option<StubConfig>,
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

    fn stub_config(&self) -> Option<StubConfig> {
        self.stub_config
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
    /// Set the stub configuration. Creates a new StubConfig Salsa input or
    /// updates the existing one. Salsa automatically invalidates downstream
    /// queries that depend on stub config fields.
    pub fn set_stub_config(
        &mut self,
        stub_paths: Vec<PathBuf>,
        builtin_stubs_dir: Option<PathBuf>,
        use_builtins: bool,
    ) -> StubConfig {
        if let Some(existing) = self.stub_config {
            existing.set_stub_paths(self).to(stub_paths);
            existing.set_builtin_stubs_dir(self).to(builtin_stubs_dir);
            existing.set_use_builtins(self).to(use_builtins);
            existing
        } else {
            let config = StubConfig::new(self, stub_paths, builtin_stubs_dir, use_builtins);
            self.stub_config = Some(config);
            config
        }
    }

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
