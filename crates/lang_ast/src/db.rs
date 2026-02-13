use std::path::PathBuf;

use dashmap::DashMap;
use rnix::Root;
use salsa::{self, Event, Setter};

#[salsa::input]
pub struct NixFile {
    path: PathBuf,
    #[return_ref]
    pub contents: String,
}

// // Wrapping this to add some traits salsa needs
// #[derive(Error, Clone, Debug, PartialEq)]
// #[error(transparent)]
// pub struct ParseError(#[from] rnix::parser::ParseError);

// impl Eq for ParseError {}

#[salsa::db]
pub trait AstDb: salsa::Database {
    // fn read_file(&self, path: PathBuf) -> Result<NixFile, std::io::Error>;

    fn parse_file(&self, file: NixFile) -> Root;
}

#[derive(Default, Clone)]
#[salsa::db]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, NixFile>,
}

#[salsa::db]
impl salsa::Database for RootDatabase {
    fn salsa_event(&self, _event: &dyn Fn() -> Event) {
        // if !tracing::enabled!(tracing::Level::TRACE) {
        //     return;
        // }

        // let event = event();
        // if matches!(event.kind, salsa::EventKind::WillCheckCancellation { .. }) {
        //     return;
        // }

        // tracing::trace!("Salsa event: {event:?}");
    }
}

#[salsa::db]
impl AstDb for RootDatabase {
    // TODO: I don't think this will be tracked by salsa so will re-parse if called many times
    // Root is !Send + !Sync so having it tracked by salsa is sad.
    // Could store it in the db itself but would need to handle re-parsing on file change
    fn parse_file(&self, file: NixFile) -> Root {
        let src = file.contents(self);
        rnix::Root::parse(src).tree()
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
