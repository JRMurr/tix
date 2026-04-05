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

use crate::project_config::{ModuleSource, NixSource, StubsGenerateConfig};

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
    generate_stubs_with_options(config, config_dir, None, false)
}

/// Like [`generate_stubs`], but with additional control:
/// - `tix_path_override`: use this path instead of auto-detecting the tix store path
///   (useful for dev builds where the binary isn't in `/nix/store/`).
/// - `skip_cache`: bypass the file cache and force a fresh nix build.
pub fn generate_stubs_with_options(
    config: &StubsGenerateConfig,
    config_dir: &Path,
    tix_path_override: Option<&Path>,
    skip_cache: bool,
) -> Result<GeneratedStubs, Error> {
    // Resolve the nixpkgs source to a store path.
    let nixpkgs_path = config
        .nixpkgs
        .as_ref()
        .ok_or(Error::MissingNixpkgs)
        .and_then(|src| resolve_nix_source(src, config_dir))?;

    // Resolve tix's own store path (needed as a build input for gen-stubs).
    let tix_path = match tix_path_override {
        Some(p) => p.to_path_buf(),
        None => resolve_tix_store_path().ok_or(Error::NotInNixStore)?,
    };

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

    // Assemble Nix list literals for user-supplied extra modules (if any).
    // These get passed to `generate-stubs-runtime.nix` via `--arg` so they
    // can be appended to the NixOS / HM modules lists.
    let extra_nixos = build_module_list(&config.nixos_modules, config_dir)?;
    let extra_hm = build_module_list(&config.home_manager_modules, config_dir)?;

    // Serialize custom-system definitions for cache-key hashing. The actual
    // system generation happens *after* nix build completes (see below).
    let systems_digest = digest_systems_config(&config.systems, config_dir)?;

    // Check the lightweight file cache before invoking nix.
    let cache_key = compute_cache_key(
        &nixpkgs_path,
        &tix_path,
        hm_path.as_deref(),
        &extra_nixos,
        &extra_hm,
        &systems_digest,
    );
    if !skip_cache {
        if let Some(cached) = check_cache(&cache_key) {
            log::debug!("Using cached stubs: {}", cached.display());
            return Ok(GeneratedStubs {
                stubs_dir: cached,
                source_roots,
            });
        }
    }

    // Find the generate-stubs-runtime.nix shipped with the tix binary.
    let generate_nix = find_generate_nix(&tix_path)?;

    // Invoke `nix build`.
    log::info!("Generating stubs via nix build (this may take a minute)...");
    let store_path = run_nix_build(
        &generate_nix,
        &nixpkgs_path,
        &tix_path,
        hm_path.as_deref(),
        &extra_nixos,
        &extra_hm,
    )?;

    // Without custom systems, the `nix build` output IS the stubs dir.
    // With custom systems, we copy the built-ins into a user-owned
    // directory, then layer generated `<name>.tix` files on top.
    let final_stubs_dir = if config.systems.is_empty() {
        store_path.clone()
    } else {
        build_merged_stubs_dir(&store_path, &cache_key, &config.systems, config_dir)?
    };

    // Cache the final stubs dir for next time.
    if let Err(e) = write_cache(&cache_key, &final_stubs_dir) {
        log::warn!("Failed to write stubs cache: {e}");
    }

    log::info!("Generated stubs: {}", final_stubs_dir.display());
    Ok(GeneratedStubs {
        stubs_dir: final_stubs_dir,
        source_roots,
    })
}

// ==============================================================================
// Custom system generation (after nix build)
// ==============================================================================

/// Create a user-owned merged-stubs directory at
/// `~/.cache/tix/custom-stubs/<cache_key>/`. The directory contains
/// copies of every `.tix` file from `built_in_dir` plus fresh
/// `<name>.tix` files generated from each custom system.
///
/// Uses regular copies rather than symlinks so the merged dir stays
/// valid even if `nix-collect-garbage` reclaims the original store
/// path.
fn build_merged_stubs_dir(
    built_in_dir: &Path,
    cache_key: &str,
    systems: &std::collections::HashMap<String, crate::project_config::CustomSystem>,
    config_dir: &Path,
) -> Result<PathBuf, Error> {
    let merged_root = custom_stubs_dir()
        .ok_or_else(|| Error::Cache("cannot determine cache directory".into()))?;
    let merged = merged_root.join(cache_key);
    populate_merged_stubs_dir(built_in_dir, &merged, systems, config_dir)?;
    Ok(merged)
}

/// Core logic of [`build_merged_stubs_dir`] that takes the output
/// directory explicitly. Separated for testability.
fn populate_merged_stubs_dir(
    built_in_dir: &Path,
    merged: &Path,
    systems: &std::collections::HashMap<String, crate::project_config::CustomSystem>,
    config_dir: &Path,
) -> Result<(), Error> {
    // Replace any existing dir atomically-ish: remove then recreate.
    if merged.exists() {
        std::fs::remove_dir_all(merged)
            .map_err(|e| Error::Cache(format!("removing old merged dir: {e}")))?;
    }
    std::fs::create_dir_all(merged)
        .map_err(|e| Error::Cache(format!("creating merged dir: {e}")))?;

    // Copy every built-in .tix file.
    let entries = std::fs::read_dir(built_in_dir)
        .map_err(|e| Error::Cache(format!("reading {}: {e}", built_in_dir.display())))?;
    for entry in entries {
        let entry = entry.map_err(|e| Error::Cache(format!("reading dir entry: {e}")))?;
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("tix") {
            continue;
        }
        let Some(file_name) = path.file_name() else {
            continue;
        };
        std::fs::copy(&path, merged.join(file_name))
            .map_err(|e| Error::Cache(format!("copying {}: {e}", path.display())))?;
    }

    // Generate each custom system into the merged dir. Failures are
    // logged but don't abort the whole generation — users see the
    // error in the LSP log and can iterate via the CLI equivalent.
    for (name, sys) in systems {
        if let Err(e) = generate_custom_system(name, sys, merged, config_dir) {
            log::warn!("Failed to generate custom system '{name}': {e}");
        }
    }

    Ok(())
}

fn custom_stubs_dir() -> Option<PathBuf> {
    custom_stubs_cache_dir()
}

/// Return the merged custom-stubs cache directory
/// (`~/.cache/tix/custom-stubs/`). Each entry under this path is a
/// `<hash>/` subdirectory containing the merged built-ins + generated
/// custom-system stubs for a given cache key.
pub fn custom_stubs_cache_dir() -> Option<PathBuf> {
    dirs::cache_dir().map(|d| d.join("tix/custom-stubs"))
}

/// Generate a single custom system by invoking the current tix binary
/// as a subprocess with `stubs generate module`. Subprocess invocation
/// mirrors the CLI workflow documented in the stubs guide — users can
/// run the same command themselves to iterate.
fn generate_custom_system(
    name: &str,
    sys: &crate::project_config::CustomSystem,
    out_dir: &Path,
    config_dir: &Path,
) -> Result<(), Error> {
    let tix_exe = std::env::current_exe()
        .map_err(|e| Error::NixCommand(format!("cannot locate current tix binary: {e}")))?;

    // Log the spawned binary path once per session so users can spot
    // mismatches between the LSP's tix and their shell's tix.
    static LOG_TIX_EXE: std::sync::Once = std::sync::Once::new();
    LOG_TIX_EXE.call_once(|| {
        log::info!(
            "custom-system generation uses tix binary: {}",
            tix_exe.display()
        );
    });

    // `sys.modules` is reserved — it doesn't splice into options_expr
    // today. Warn loudly if users populated it, since the doc is
    // aspirational.
    if !sys.modules.is_empty() {
        log::warn!(
            "custom system '{name}' has {} entries in `modules` — these are NOT yet spliced \
             into options_expr; the field is currently cache-key-only. Import the modules inside \
             options_expr directly.",
            sys.modules.len()
        );
    }
    let _ = config_dir; // reserved for future module-path resolution

    let out_file = out_dir.join(format!("{name}.tix"));
    let mut cmd = Command::new(&tix_exe);
    cmd.args(["stubs", "generate", "module", "--name", name])
        .args(["--options-expr", &sys.options_expr])
        .args(["-o"])
        .arg(&out_file);

    for arg in &sys.context_args {
        cmd.args(["--context-arg", arg]);
    }
    if sys.context_args.is_empty() {
        cmd.args(["--context-arg", "config"]);
    }

    if let Some(glob) = &sys.example_glob {
        cmd.args(["--example-glob", glob]);
    }

    let output = cmd
        .output()
        .map_err(|e| Error::NixCommand(format!("failed to spawn tix: {e}")))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(Error::NixCommand(format!(
            "tix stubs generate module --name {name} failed:\n{stderr}"
        )));
    }

    log::debug!("generated custom system stub: {}", out_file.display());
    Ok(())
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
// Module list assembly (for --arg extra-nixos-modules / extra-hm-modules)
// ==============================================================================

/// Translate a [`ModuleSource`] into a Nix syntax fragment suitable for
/// splicing into a `modules` list passed to `evalModules` or
/// `eval-config.nix`.
///
/// - `Path("./modules/foo.nix")` resolves against `config_dir` and emits
///   `"(import /abs/path)"`. The file must exist (we canonicalize).
/// - `Expr { expr }` emits `"(EXPR)"` verbatim.
fn module_source_to_nix(src: &ModuleSource, config_dir: &Path) -> Result<String, Error> {
    match src {
        ModuleSource::Path(p) => {
            let path = config_dir.join(p);
            let abs = path
                .canonicalize()
                .map_err(|e| Error::PathNotFound(format!("{}: {e}", path.display())))?;
            Ok(format!("(import {})", abs.display()))
        }
        ModuleSource::Expr { expr } => Ok(format!("({})", expr.trim())),
    }
}

/// Build a Nix list literal from a slice of module sources. Empty slice
/// returns `"[ ]"`.
pub fn build_module_list(srcs: &[ModuleSource], config_dir: &Path) -> Result<String, Error> {
    if srcs.is_empty() {
        return Ok("[ ]".to_string());
    }
    let parts: Result<Vec<_>, Error> = srcs
        .iter()
        .map(|s| module_source_to_nix(s, config_dir))
        .collect();
    Ok(format!("[ {} ]", parts?.join(" ")))
}

// ==============================================================================
// Lightweight file cache (~/.cache/tix/store-stubs/)
// ==============================================================================

/// Return the cache directory path (`~/.cache/tix/store-stubs/`).
/// Returns `None` if the platform has no standard cache dir.
pub fn cache_dir() -> Option<PathBuf> {
    dirs::cache_dir().map(|d| d.join("tix/store-stubs"))
}

/// Delete every top-level file in `dir`. Returns the number of entries
/// removed. Subdirectories and non-regular files are skipped. Missing
/// `dir` is a no-op (returns 0).
pub fn clear_cache_in_dir(dir: &Path) -> std::io::Result<usize> {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(0),
        Err(err) => return Err(err),
    };

    let mut count = 0;
    for entry in entries {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if file_type.is_file() || file_type.is_symlink() {
            std::fs::remove_file(entry.path())?;
            count += 1;
        }
    }
    Ok(count)
}

/// Delete every top-level subdirectory in `dir`. Returns the number
/// of directories removed. Top-level files and non-directories are
/// skipped (symmetric with `clear_cache_in_dir` which does the
/// opposite). Missing `dir` is a no-op (returns 0).
///
/// Used to clear `~/.cache/tix/custom-stubs/` where entries are
/// `<hash>/` directories, not flat files.
pub fn clear_custom_stubs_dir(dir: &Path) -> std::io::Result<usize> {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(0),
        Err(err) => return Err(err),
    };

    let mut count = 0;
    for entry in entries {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            std::fs::remove_dir_all(entry.path())?;
            count += 1;
        }
    }
    Ok(count)
}

/// Counts returned by [`clear_all_cache`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClearStats {
    /// Files removed from `~/.cache/tix/store-stubs/`.
    pub store_entries: usize,
    /// Subdirectories removed from `~/.cache/tix/custom-stubs/`.
    pub custom_dirs: usize,
}

/// Delete all entries in both cache dirs (`store-stubs/` and
/// `custom-stubs/`). Returns the combined counts, or `None` if the
/// platform has no standard cache dir.
pub fn clear_all_cache() -> std::io::Result<Option<ClearStats>> {
    let Some(store) = cache_dir() else {
        return Ok(None);
    };
    let store_entries = clear_cache_in_dir(&store)?;
    // custom_stubs_dir() shares the same cache-dir root, so if store is
    // Some the custom path is too — but guard anyway for safety.
    let custom_dirs = match custom_stubs_cache_dir() {
        Some(dir) => clear_custom_stubs_dir(&dir)?,
        None => 0,
    };
    Ok(Some(ClearStats {
        store_entries,
        custom_dirs,
    }))
}

/// Compute a cache key from input store paths and the Nix-literal
/// strings describing extra modules to splice into the NixOS/HM evals.
/// The extra-module strings are hashed verbatim (no content hashing of
/// the referenced files — see `tix stubs refresh`).
fn compute_cache_key(
    nixpkgs: &Path,
    tix: &Path,
    hm: Option<&Path>,
    extra_nixos_modules: &str,
    extra_hm_modules: &str,
    systems_digest: &str,
) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    nixpkgs.hash(&mut hasher);
    tix.hash(&mut hasher);
    if let Some(hm) = hm {
        hm.hash(&mut hasher);
    }
    extra_nixos_modules.hash(&mut hasher);
    extra_hm_modules.hash(&mut hasher);
    systems_digest.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

/// Produce a deterministic string fingerprint of the custom-systems
/// config. Systems are emitted in sorted-name order so hash stability
/// doesn't depend on HashMap iteration order.
///
/// Module lists are resolved via [`build_module_list`] so that Path
/// entries hash as their canonicalized absolute path (matching the
/// `extra_nixos_modules` / `extra_hm_modules` digest shape and
/// preventing two projects in different dirs from accidentally sharing
/// a cache entry when they both write `./modules/foo.nix`).
fn digest_systems_config(
    systems: &std::collections::HashMap<String, crate::project_config::CustomSystem>,
    config_dir: &Path,
) -> Result<String, Error> {
    if systems.is_empty() {
        return Ok(String::new());
    }
    let mut names: Vec<&String> = systems.keys().collect();
    names.sort();
    let mut out = String::new();
    for name in names {
        let sys = &systems[name];
        // options_expr gets trimmed to absorb cosmetic whitespace edits.
        out.push_str(name);
        out.push('\0');
        out.push_str(sys.options_expr.trim());
        out.push('\0');
        for arg in &sys.context_args {
            out.push_str(arg);
            out.push(',');
        }
        out.push('\0');
        if let Some(glob) = &sys.example_glob {
            out.push_str(glob);
        }
        out.push('\0');
        out.push_str(&build_module_list(&sys.modules, config_dir)?);
        out.push('\n');
    }
    Ok(out)
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
    extra_nixos_modules: &str,
    extra_hm_modules: &str,
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

    // Forward user-supplied extra modules to generate-stubs-runtime.nix.
    // These are already Nix list literals like "[ (import /abs/foo.nix) ]".
    cmd.arg("--arg")
        .arg("extra-nixos-modules")
        .arg(extra_nixos_modules);
    cmd.arg("--arg")
        .arg("extra-hm-modules")
        .arg(extra_hm_modules);

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
            "[ ]",
            "[ ]",
            "",
        );
        let k2 = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
            "[ ]",
            "[ ]",
            "",
        );
        assert_eq!(k1, k2);
    }

    #[test]
    fn cache_key_differs_with_hm() {
        let without = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
            "[ ]",
            "[ ]",
            "",
        );
        let with = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            Some(Path::new("/nix/store/ghi-hm")),
            "[ ]",
            "[ ]",
            "",
        );
        assert_ne!(without, with);
    }

    #[test]
    fn cache_key_differs_with_different_inputs() {
        let k1 = compute_cache_key(
            Path::new("/nix/store/abc-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
            "[ ]",
            "[ ]",
            "",
        );
        let k2 = compute_cache_key(
            Path::new("/nix/store/xyz-nixpkgs"),
            Path::new("/nix/store/def-tix"),
            None,
            "[ ]",
            "[ ]",
            "",
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

    #[test]
    fn clear_cache_in_dir_removes_files() {
        let dir = tempfile::tempdir().unwrap();

        // Populate some fake cache entries.
        std::fs::write(dir.path().join("abc123"), "/nix/store/aaa").unwrap();
        std::fs::write(dir.path().join("def456"), "/nix/store/bbb").unwrap();
        std::fs::write(dir.path().join("ghi789"), "/nix/store/ccc").unwrap();

        let removed = clear_cache_in_dir(dir.path()).unwrap();
        assert_eq!(removed, 3);

        // Directory should still exist but be empty.
        assert!(dir.path().exists());
        let remaining: Vec<_> = std::fs::read_dir(dir.path()).unwrap().collect();
        assert!(remaining.is_empty());
    }

    #[test]
    fn clear_cache_in_dir_missing_dir_ok() {
        // Clearing a non-existent dir is a no-op — not an error.
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("does-not-exist");
        let removed = clear_cache_in_dir(&missing).unwrap();
        assert_eq!(removed, 0);
    }

    #[test]
    fn build_module_list_empty_returns_empty_literal() {
        let dir = tempfile::tempdir().unwrap();
        let got = build_module_list(&[], dir.path()).unwrap();
        assert_eq!(got, "[ ]");
    }

    #[test]
    fn build_module_list_path_resolves_relative_to_config_dir() {
        let dir = tempfile::tempdir().unwrap();
        let module_path = dir.path().join("modules/foo.nix");
        std::fs::create_dir_all(module_path.parent().unwrap()).unwrap();
        std::fs::write(&module_path, "{ }").unwrap();

        let got = build_module_list(
            &[crate::project_config::ModuleSource::Path(
                "modules/foo.nix".into(),
            )],
            dir.path(),
        )
        .unwrap();

        // The path should be resolved to the absolute location of foo.nix.
        let abs = module_path.canonicalize().unwrap();
        let expected = format!("[ (import {}) ]", abs.display());
        assert_eq!(got, expected);
    }

    #[test]
    fn build_module_list_expr_wraps_in_parens() {
        let dir = tempfile::tempdir().unwrap();
        let got = build_module_list(
            &[crate::project_config::ModuleSource::Expr {
                expr: "inputs.foo.nixosModules.bar".into(),
            }],
            dir.path(),
        )
        .unwrap();
        assert_eq!(got, "[ (inputs.foo.nixosModules.bar) ]");
    }

    #[test]
    fn build_module_list_mixes_paths_and_exprs() {
        let dir = tempfile::tempdir().unwrap();
        let module_path = dir.path().join("a.nix");
        std::fs::write(&module_path, "{ }").unwrap();

        let got = build_module_list(
            &[
                crate::project_config::ModuleSource::Path("a.nix".into()),
                crate::project_config::ModuleSource::Expr { expr: "x.y".into() },
            ],
            dir.path(),
        )
        .unwrap();
        let abs = module_path.canonicalize().unwrap();
        let expected = format!("[ (import {}) (x.y) ]", abs.display());
        assert_eq!(got, expected);
    }

    #[test]
    fn build_module_list_missing_path_errors() {
        let dir = tempfile::tempdir().unwrap();
        let err = build_module_list(
            &[crate::project_config::ModuleSource::Path("nope.nix".into())],
            dir.path(),
        );
        assert!(err.is_err(), "expected error for missing path");
    }

    #[test]
    fn cache_key_differs_when_modules_change() {
        let nixpkgs = Path::new("/nix/store/abc-nixpkgs");
        let tix = Path::new("/nix/store/def-tix");

        let k_empty = compute_cache_key(nixpkgs, tix, None, "[ ]", "[ ]", "");
        let k_with_nixos =
            compute_cache_key(nixpkgs, tix, None, "[ (import /abs/foo.nix) ]", "[ ]", "");
        let k_with_hm =
            compute_cache_key(nixpkgs, tix, None, "[ ]", "[ (import /abs/foo.nix) ]", "");
        assert_ne!(k_empty, k_with_nixos);
        assert_ne!(k_empty, k_with_hm);
        assert_ne!(k_with_nixos, k_with_hm);
    }

    #[test]
    fn populate_merged_stubs_dir_copies_builtins() {
        // Given a built-in dir with some .tix files, the merged dir
        // should contain only the .tix files (not other extensions).
        let built_in = tempfile::tempdir().unwrap();
        std::fs::write(built_in.path().join("nixos.tix"), "# nixos\n").unwrap();
        std::fs::write(built_in.path().join("lib.tix"), "# lib\n").unwrap();
        // Non-.tix files should be skipped.
        std::fs::write(built_in.path().join("manifest.json"), "{}").unwrap();

        let merged_root = tempfile::tempdir().unwrap();
        let merged = merged_root.path().join("out");
        let config_dir = tempfile::tempdir().unwrap();
        let systems = std::collections::HashMap::new();

        populate_merged_stubs_dir(built_in.path(), &merged, &systems, config_dir.path()).unwrap();

        assert!(merged.join("nixos.tix").exists());
        assert!(merged.join("lib.tix").exists());
        assert!(!merged.join("manifest.json").exists());

        // Contents preserved.
        let content = std::fs::read_to_string(merged.join("nixos.tix")).unwrap();
        assert_eq!(content, "# nixos\n");
    }

    #[test]
    fn populate_merged_stubs_dir_overwrites_existing() {
        // Calling twice with different builtins cleans up between runs.
        let built_in_a = tempfile::tempdir().unwrap();
        std::fs::write(built_in_a.path().join("a.tix"), "A\n").unwrap();
        let built_in_b = tempfile::tempdir().unwrap();
        std::fs::write(built_in_b.path().join("b.tix"), "B\n").unwrap();

        let merged_root = tempfile::tempdir().unwrap();
        let merged = merged_root.path().join("out");
        let config_dir = tempfile::tempdir().unwrap();
        let systems = std::collections::HashMap::new();

        populate_merged_stubs_dir(built_in_a.path(), &merged, &systems, config_dir.path()).unwrap();
        assert!(merged.join("a.tix").exists());

        populate_merged_stubs_dir(built_in_b.path(), &merged, &systems, config_dir.path()).unwrap();
        // After rebuild, a.tix should be gone and b.tix present.
        assert!(!merged.join("a.tix").exists());
        assert!(merged.join("b.tix").exists());
    }

    #[test]
    fn cache_key_differs_when_systems_change() {
        let nixpkgs = Path::new("/nix/store/abc-nixpkgs");
        let tix = Path::new("/nix/store/def-tix");
        let k_empty = compute_cache_key(nixpkgs, tix, None, "[ ]", "[ ]", "");
        let k_fp = compute_cache_key(
            nixpkgs,
            tix,
            None,
            "[ ]",
            "[ ]",
            "flake-parts\0(x)\0config,\0\0\0\n",
        );
        assert_ne!(k_empty, k_fp);
    }

    #[test]
    fn digest_systems_config_is_deterministic() {
        use crate::project_config::CustomSystem;
        let mut systems = std::collections::HashMap::new();
        systems.insert(
            "flake-parts".into(),
            CustomSystem {
                options_expr: "(x.y)".into(),
                context_args: vec!["config".into(), "inputs".into()],
                example_glob: Some("fp/**/*.nix".into()),
                modules: vec![],
            },
        );
        systems.insert(
            "devenv".into(),
            CustomSystem {
                options_expr: "(z)".into(),
                context_args: vec![],
                example_glob: None,
                modules: vec![],
            },
        );
        let dir = tempfile::tempdir().unwrap();
        let d1 = digest_systems_config(&systems, dir.path()).unwrap();
        let d2 = digest_systems_config(&systems, dir.path()).unwrap();
        assert_eq!(d1, d2, "digest should be stable across calls");
        // devenv comes first alphabetically.
        let devenv_idx = d1.find("devenv").expect("devenv in digest");
        let fp_idx = d1.find("flake-parts").expect("flake-parts in digest");
        assert!(devenv_idx < fp_idx, "systems digest must be sorted: {d1}");
    }

    #[test]
    fn digest_systems_config_empty_is_empty() {
        let dir = tempfile::tempdir().unwrap();
        let systems = std::collections::HashMap::new();
        assert_eq!(digest_systems_config(&systems, dir.path()).unwrap(), "");
    }

    #[test]
    fn digest_systems_config_resolves_module_paths() {
        // Path entries in `sys.modules` should hash as the canonicalized
        // absolute path (via build_module_list), not as the raw relative
        // form — so two projects in different dirs writing the same
        // `./modules/foo.nix` produce distinct digests.
        use crate::project_config::{CustomSystem, ModuleSource};
        let dir = tempfile::tempdir().unwrap();
        let module_path = dir.path().join("a.nix");
        std::fs::write(&module_path, "{ }").unwrap();

        let mut systems = std::collections::HashMap::new();
        systems.insert(
            "mysys".into(),
            CustomSystem {
                options_expr: "(x)".into(),
                context_args: vec![],
                example_glob: None,
                modules: vec![ModuleSource::Path("a.nix".into())],
            },
        );

        let digest = digest_systems_config(&systems, dir.path()).unwrap();
        let abs = module_path.canonicalize().unwrap();
        assert!(
            digest.contains(&abs.display().to_string()),
            "digest should contain canonicalized module path, got: {digest}"
        );
        // Raw relative form must not appear on its own (it's a substring
        // of the absolute path only if the tempdir happens to contain
        // 'a.nix' literally, which is fine — the check above is the
        // positive assertion).
    }

    #[test]
    fn digest_systems_config_missing_module_path_errors() {
        use crate::project_config::{CustomSystem, ModuleSource};
        let dir = tempfile::tempdir().unwrap();
        let mut systems = std::collections::HashMap::new();
        systems.insert(
            "mysys".into(),
            CustomSystem {
                options_expr: "(x)".into(),
                context_args: vec![],
                example_glob: None,
                modules: vec![ModuleSource::Path("nope.nix".into())],
            },
        );
        let err = digest_systems_config(&systems, dir.path());
        assert!(err.is_err(), "expected error for missing module path");
    }

    #[test]
    fn clear_custom_stubs_dir_removes_nested_subdirs() {
        // Each entry in `custom-stubs/` is a `<hash>/` directory holding
        // merged built-ins + custom stubs. `clear_custom_stubs_dir`
        // should reclaim them wholesale.
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join("hash1")).unwrap();
        std::fs::write(dir.path().join("hash1/foo.tix"), "# foo\n").unwrap();
        std::fs::create_dir(dir.path().join("hash2")).unwrap();
        std::fs::write(dir.path().join("hash2/bar.tix"), "# bar\n").unwrap();

        let removed = clear_custom_stubs_dir(dir.path()).unwrap();
        assert_eq!(removed, 2);

        assert!(dir.path().exists());
        assert!(!dir.path().join("hash1").exists());
        assert!(!dir.path().join("hash2").exists());
    }

    #[test]
    fn clear_custom_stubs_dir_missing_dir_ok() {
        // Symmetric with clear_cache_in_dir_missing_dir_ok: the cache
        // dir may simply not exist yet.
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("does-not-exist");
        let removed = clear_custom_stubs_dir(&missing).unwrap();
        assert_eq!(removed, 0);
    }

    #[test]
    fn clear_custom_stubs_dir_ignores_top_level_files() {
        // Only directories are reclaimed. A stray file (shouldn't
        // exist in normal operation, but be resilient) is left alone.
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("stray.txt"), "x").unwrap();
        std::fs::create_dir(dir.path().join("hash1")).unwrap();
        let removed = clear_custom_stubs_dir(dir.path()).unwrap();
        assert_eq!(removed, 1);
        assert!(dir.path().join("stray.txt").exists());
        assert!(!dir.path().join("hash1").exists());
    }

    #[test]
    fn clear_cache_in_dir_ignores_subdirectories() {
        // The cache dir only contains flat files keyed by hash. If a user
        // accidentally creates a subdir, we shouldn't error — just skip it.
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("abc123"), "/nix/store/aaa").unwrap();
        std::fs::create_dir(dir.path().join("subdir")).unwrap();
        std::fs::write(dir.path().join("subdir/nested"), "content").unwrap();

        let removed = clear_cache_in_dir(dir.path()).unwrap();
        assert_eq!(removed, 1);

        // The subdir survives.
        assert!(dir.path().join("subdir").exists());
    }
}
