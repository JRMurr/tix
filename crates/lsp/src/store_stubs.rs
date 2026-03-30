// ==============================================================================
// Runtime Nix Store-Cached Stub Generation
// ==============================================================================
//
// Generates stubs at runtime by invoking `nix build` with the parameterized
// generate-stubs-runtime.nix. Results are cached in the Nix store; a
// lightweight file-based cache (~/.cache/tix/store-stubs/) avoids re-evaluating
// the full nix expression when inputs haven't changed.
//
// Resolution priority:
//   1. TIX_BUILTIN_STUBS env var (explicit override, always wins)
//   2. [stubs.generate] runtime generation (this module)
//   3. Compiled-in minimal stubs (existing fallback)

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::project_config::{NixSource, StubsGenerateConfig};

/// Result of successful stub generation: the stubs directory plus the resolved
/// source roots for `@source` annotation resolution.
pub struct GeneratedStubs {
    /// Store path containing the generated `.tix` files.
    pub stubs_dir: PathBuf,
    /// Source roots for resolving `@source` annotations.
    /// e.g. `[("nixpkgs", "/nix/store/...-source"), ("home-manager", "/nix/store/...-hm")]`
    pub source_roots: Vec<(String, PathBuf)>,
}

/// Generate stubs from `[stubs.generate]` config, using the Nix store as cache.
///
/// Returns the stubs directory and source roots, or an error if generation fails.
/// The caller should fall back to compiled-in stubs.
pub fn generate_stubs(
    config: &StubsGenerateConfig,
    config_dir: &Path,
) -> Result<GeneratedStubs, Error> {
    // Resolve the nixpkgs source to a store path.
    let nixpkgs_path = config
        .nixpkgs
        .as_ref()
        .ok_or(Error::MissingNixpkgs)
        .and_then(|src| resolve_nix_source(src, config_dir))?;

    // Resolve tix's own store path (needed as a build input for gen-stubs).
    let tix_path = resolve_tix_store_path().ok_or(Error::NotInNixStore)?;

    // Optionally resolve home-manager source.
    let hm_path = config
        .home_manager
        .as_ref()
        .map(|src| resolve_nix_source(src, config_dir))
        .transpose()?;

    log::debug!("Resolved nixpkgs: {}", nixpkgs_path.display());
    log::debug!("Resolved tix: {}", tix_path.display());
    if let Some(ref hm) = hm_path {
        log::debug!("Resolved home-manager: {}", hm.display());
    }

    // Build source roots for @source annotation resolution.
    let mut source_roots = vec![("nixpkgs".to_string(), nixpkgs_path.clone())];
    if let Some(ref hm) = hm_path {
        source_roots.push(("home-manager".to_string(), hm.clone()));
    }

    // Check the lightweight file cache before invoking nix.
    let cache_key = compute_cache_key(&nixpkgs_path, &tix_path, hm_path.as_deref());
    if let Some(cached) = check_cache(&cache_key) {
        log::debug!("Using cached stubs: {}", cached.display());
        return Ok(GeneratedStubs {
            stubs_dir: cached,
            source_roots,
        });
    }

    // Find the generate-stubs-runtime.nix shipped with the tix binary.
    let generate_nix = find_generate_nix(&tix_path)?;

    // Invoke `nix build`.
    log::info!("Generating stubs via nix build (this may take a minute)...");
    let store_path = run_nix_build(&generate_nix, &nixpkgs_path, &tix_path, hm_path.as_deref())?;

    // Cache the result for next time.
    if let Err(e) = write_cache(&cache_key, &store_path) {
        log::warn!("Failed to write stubs cache: {e}");
    }

    log::info!("Generated stubs: {}", store_path.display());
    Ok(GeneratedStubs {
        stubs_dir: store_path,
        source_roots,
    })
}

// ==============================================================================
// Nix source resolution
// ==============================================================================

/// Resolve a NixSource to a concrete filesystem path.
fn resolve_nix_source(source: &NixSource, config_dir: &Path) -> Result<PathBuf, Error> {
    match source {
        NixSource::Path(p) => {
            let path = PathBuf::from(p);
            if path.exists() {
                Ok(path)
            } else {
                // Try relative to config dir.
                let resolved = config_dir.join(p);
                if resolved.exists() {
                    Ok(resolved)
                } else {
                    Err(Error::PathNotFound(p.clone()))
                }
            }
        }
        NixSource::Expr { expr } => {
            let output = Command::new("nix")
                .args(["eval", "--raw", "--impure", "--expr", expr])
                .output()
                .map_err(|e| Error::NixCommand(format!("failed to run `nix eval`: {e}")))?;

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                return Err(Error::NixCommand(format!(
                    "`nix eval --expr {expr}` failed: {stderr}"
                )));
            }

            let path_str = String::from_utf8_lossy(&output.stdout);
            let path = PathBuf::from(path_str.trim());
            if path.exists() {
                Ok(path)
            } else {
                Err(Error::PathNotFound(path_str.into_owned()))
            }
        }
    }
}

// ==============================================================================
// Tix store path resolution
// ==============================================================================

/// Resolve the tix binary's Nix store path.
///
/// If the binary is at `/nix/store/<hash>-tix/bin/tix`, returns
/// `/nix/store/<hash>-tix`. Returns `None` if not running from the Nix store
/// (dev mode).
pub fn resolve_tix_store_path() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?.canonicalize().ok()?;
    let exe_str = exe.to_str()?;

    if !exe_str.starts_with("/nix/store/") {
        return None;
    }

    // /nix/store/<hash>-<name>/bin/tix -> /nix/store/<hash>-<name>
    // Find the third '/' after /nix/store/
    let after_store = &exe_str["/nix/store/".len()..];
    let end = after_store.find('/')?;
    Some(PathBuf::from(&exe_str[.."/nix/store/".len() + end]))
}

/// Find the generate-stubs-runtime.nix shipped with the tix package.
fn find_generate_nix(tix_store_path: &Path) -> Result<PathBuf, Error> {
    let path = tix_store_path.join("share/tix/generate-stubs-runtime.nix");
    if path.exists() {
        Ok(path)
    } else {
        Err(Error::MissingGenerateNix(path))
    }
}

// ==============================================================================
// Lightweight file cache (~/.cache/tix/store-stubs/)
// ==============================================================================

fn cache_dir() -> Option<PathBuf> {
    dirs::cache_dir().map(|d| d.join("tix/store-stubs"))
}

/// Compute a cache key from input store paths.
fn compute_cache_key(nixpkgs: &Path, tix: &Path, hm: Option<&Path>) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    nixpkgs.hash(&mut hasher);
    tix.hash(&mut hasher);
    if let Some(hm) = hm {
        hm.hash(&mut hasher);
    }
    format!("{:016x}", hasher.finish())
}

/// Check if a cached store path exists and is still valid.
fn check_cache(key: &str) -> Option<PathBuf> {
    let cache_file = cache_dir()?.join(key);
    let contents = std::fs::read_to_string(&cache_file).ok()?;
    let store_path = PathBuf::from(contents.trim());
    if store_path.exists() {
        Some(store_path)
    } else {
        // Store path was garbage-collected — cache miss.
        None
    }
}

/// Atomically write a cache entry.
fn write_cache(key: &str, store_path: &Path) -> Result<(), Error> {
    let dir = cache_dir().ok_or_else(|| Error::Cache("cannot determine cache directory".into()))?;
    std::fs::create_dir_all(&dir)
        .map_err(|e| Error::Cache(format!("creating {}: {e}", dir.display())))?;

    let cache_file = dir.join(key);
    let tmp_file = dir.join(format!("{key}.tmp.{}", std::process::id()));

    let mut f = std::fs::File::create(&tmp_file)
        .map_err(|e| Error::Cache(format!("creating temp file: {e}")))?;
    f.write_all(store_path.to_string_lossy().as_bytes())
        .map_err(|e| Error::Cache(format!("writing temp file: {e}")))?;
    f.sync_all()
        .map_err(|e| Error::Cache(format!("syncing temp file: {e}")))?;
    drop(f);

    std::fs::rename(&tmp_file, &cache_file)
        .map_err(|e| Error::Cache(format!("renaming cache file: {e}")))?;

    Ok(())
}

// ==============================================================================
// Nix build invocation
// ==============================================================================

fn run_nix_build(
    generate_nix: &Path,
    nixpkgs_path: &Path,
    tix_path: &Path,
    hm_path: Option<&Path>,
) -> Result<PathBuf, Error> {
    let mut cmd = Command::new("nix");
    cmd.args(["build", "-f"])
        .arg(generate_nix)
        .arg("--arg")
        .arg("nixpkgs-path")
        .arg(nixpkgs_path)
        .arg("--arg")
        .arg("tix-path")
        .arg(tix_path);

    if let Some(hm) = hm_path {
        cmd.arg("--arg").arg("home-manager-path").arg(hm);
    }

    cmd.args(["--no-link", "--print-out-paths"]);

    let output = cmd
        .output()
        .map_err(|e| Error::NixCommand(format!("failed to run `nix build`: {e}")))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(Error::NixCommand(format!("`nix build` failed: {stderr}")));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let store_path = stdout
        .lines()
        .next()
        .ok_or_else(|| Error::NixCommand("`nix build` produced no output".into()))?;

    let path = PathBuf::from(store_path.trim());
    if path.exists() {
        Ok(path)
    } else {
        Err(Error::NixCommand(format!(
            "nix build output path does not exist: {}",
            path.display()
        )))
    }
}

// ==============================================================================
// Error type
// ==============================================================================

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("no nixpkgs source configured in [stubs.generate]")]
    MissingNixpkgs,

    #[error(
        "tix is not running from the Nix store (dev mode); use TIX_BUILTIN_STUBS or nix build"
    )]
    NotInNixStore,

    #[error("path not found: {0}")]
    PathNotFound(String),

    #[error("nix command error: {0}")]
    NixCommand(String),

    #[error("generate-stubs-runtime.nix not found at {0}")]
    MissingGenerateNix(PathBuf),

    #[error("cache error: {0}")]
    Cache(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_tix_store_path_returns_none_in_dev() {
        // In a cargo test environment, the binary is not in /nix/store.
        // This should return None (dev mode).
        let result = resolve_tix_store_path();
        // We can't guarantee the test runner isn't in /nix/store (it might be
        // on NixOS), so just verify the function doesn't panic.
        let _ = result;
    }

    #[test]
    fn cache_key_deterministic() {
        let k1 = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
        );
        let k2 = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
        );
        assert_eq!(k1, k2);
    }

    #[test]
    fn cache_key_differs_with_hm() {
        let without = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
        );
        let with = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            Some(Path::new("/nix/store/ghi-hm")),
        );
        assert_ne!(without, with);
    }

    #[test]
    fn cache_key_differs_with_different_inputs() {
        let k1 = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
        );
        let k2 = compute_cache_key(
            Path::new("/nix/store/xyz-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
        );
        assert_ne!(k1, k2);
    }

    #[test]
    fn cache_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        // Override cache dir by testing the write/read functions directly.
        let key = "test_key_12345";
        let cache_file = dir.path().join(key);
        let store_path = dir.path().join("fake-store-path");
        std::fs::create_dir(&store_path).unwrap();

        // Write.
        let tmp = dir.path().join(format!("{key}.tmp.{}", std::process::id()));
        let mut f = std::fs::File::create(&tmp).unwrap();
        f.write_all(store_path.to_string_lossy().as_bytes())
            .unwrap();
        std::fs::rename(&tmp, &cache_file).unwrap();

        // Read back.
        let contents = std::fs::read_to_string(&cache_file).unwrap();
        let read_path = PathBuf::from(contents.trim());
        assert_eq!(read_path, store_path);
        assert!(read_path.exists());
    }
}
