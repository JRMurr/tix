use std::{
    collections::{HashMap, hash_map::Entry},
    fs,
    path::{Path, PathBuf},
};

use miette::Diagnostic;
use thiserror::Error;

/// A structure to store parse results of Nix files in memory, making sure that the same file never
/// has to be parsed twice.
#[derive(Default)]
pub struct NixFileStore {
    entries: HashMap<PathBuf, NixFile>,
}

impl NixFileStore {
    /// Get the store entry for a Nix file if it exists, otherwise parse the file, insert it into
    /// the store, and return the value.
    ///
    pub fn get(&mut self, path: &Path) -> Result<&NixFile, NixFileCreateError> {
        match self.entries.entry(path.to_owned()) {
            Entry::Occupied(entry) => Ok(entry.into_mut()),
            Entry::Vacant(entry) => Ok(entry.insert(NixFile::new(path)?)),
        }
    }
}

/// A structure for storing a successfully parsed Nix file.
pub struct NixFile {
    /// The path to the file itself, for errors.
    pub path: PathBuf,
    pub syntax_root: rnix::Root,
}

#[derive(Error, Diagnostic, Debug)]
pub enum NixFileCreateError {
    #[error(transparent)]
    IoError(#[from] std::io::Error),

    #[error(transparent)]
    ParseError(#[from] rnix::parser::ParseError), // TODO: should make this nicer with mietee sources, we should have all the info we need
}

impl NixFile {
    /// Creates a new `NixFile`, failing for I/O or parse errors.
    fn new(path: impl AsRef<Path>) -> Result<NixFile, NixFileCreateError> {
        let contents = fs::read_to_string(&path)?;

        Ok(rnix::Root::parse(&contents)
            .ok()
            .map(|syntax_root| NixFile {
                path: path.as_ref().to_owned(),
                syntax_root,
            })?)
    }
}
