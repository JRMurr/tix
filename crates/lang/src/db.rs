use std::path::PathBuf;

use dashmap::DashMap;
use salsa::{self, Event};

#[salsa::input]
pub struct File {
    path: PathBuf,
    #[return_ref]
    contents: String,
}

#[salsa::db]
pub trait Db: salsa::Database {
    fn input(&self, path: PathBuf) -> Result<File, std::io::Error>;
}

#[derive(Default, Clone)]
#[salsa::db]
pub(crate) struct RootDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, File>,
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
