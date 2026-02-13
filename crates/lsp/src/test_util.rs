use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(0);

/// Generate a unique temporary file path for tests, avoiding collisions
/// when tests run in parallel.
pub fn temp_path(name: &str) -> PathBuf {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("tix_test_{}_{id}_{name}", std::process::id()))
}

/// Find the byte offset of a pattern in source text.
pub fn find_offset(src: &str, pattern: &str) -> u32 {
    src.find(pattern).expect("pattern not found in source") as u32
}
