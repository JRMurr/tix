use std::path::PathBuf;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Manifest {
    #[serde(default)]
    pub settings: Settings,
    #[serde(rename = "repo")]
    pub repos: Vec<RepoEntry>,
}

#[derive(Debug, Deserialize)]
pub struct Settings {
    #[serde(default = "default_cache_dir")]
    pub cache_dir: PathBuf,
    #[serde(default = "default_timeout")]
    pub timeout_secs: u64,
}

fn default_cache_dir() -> PathBuf {
    PathBuf::from(".repo-check-cache")
}

fn default_timeout() -> u64 {
    120
}

impl Default for Settings {
    fn default() -> Self {
        Settings {
            cache_dir: default_cache_dir(),
            timeout_secs: default_timeout(),
        }
    }
}

#[derive(Debug, Deserialize)]
pub struct RepoEntry {
    pub name: String,
    pub url: String,
    #[serde(default = "default_rev")]
    pub rev: String,
    pub subdir: Option<String>,
    // TODO: implement full clone when shallow = false
    #[serde(default = "default_true")]
    #[allow(dead_code)]
    pub shallow: bool,
    #[serde(default)]
    pub skip_init: bool,
    #[serde(default)]
    pub skip: bool,
    pub tix_toml: Option<String>,
}

fn default_rev() -> String {
    "HEAD".to_string()
}

fn default_true() -> bool {
    true
}

pub fn load_manifest(path: &std::path::Path) -> Result<Manifest, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
    let manifest: Manifest =
        toml::from_str(&content).map_err(|e| format!("failed to parse {}: {e}", path.display()))?;

    // Validate: no duplicate names.
    let mut seen = std::collections::HashSet::new();
    for repo in &manifest.repos {
        if !seen.insert(&repo.name) {
            return Err(format!("duplicate repo name: {}", repo.name).into());
        }
    }

    Ok(manifest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_minimal_manifest() {
        let toml = r#"
[[repo]]
name = "test-repo"
url = "https://github.com/example/repo"
"#;
        let manifest: Manifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.repos.len(), 1);
        assert_eq!(manifest.repos[0].name, "test-repo");
        assert_eq!(manifest.repos[0].rev, "HEAD");
        assert!(manifest.repos[0].shallow);
        assert!(!manifest.repos[0].skip);
        assert!(!manifest.repos[0].skip_init);
        assert!(manifest.repos[0].subdir.is_none());
        assert!(manifest.repos[0].tix_toml.is_none());
    }

    #[test]
    fn parse_full_manifest() {
        let toml = r#"
[settings]
cache_dir = "/tmp/cache"
timeout_secs = 60

[[repo]]
name = "repo-a"
url = "https://github.com/a/a"
rev = "main"
subdir = "lib"
shallow = false
skip_init = true
tix_toml = "[project]\n"

[[repo]]
name = "repo-b"
url = "https://github.com/b/b"
skip = true
"#;
        let manifest: Manifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.settings.cache_dir, PathBuf::from("/tmp/cache"));
        assert_eq!(manifest.settings.timeout_secs, 60);
        assert_eq!(manifest.repos.len(), 2);

        let a = &manifest.repos[0];
        assert_eq!(a.rev, "main");
        assert_eq!(a.subdir.as_deref(), Some("lib"));
        assert!(!a.shallow);
        assert!(a.skip_init);
        assert!(a.tix_toml.is_some());

        let b = &manifest.repos[1];
        assert!(b.skip);
    }

    #[test]
    fn default_settings() {
        let toml = r#"
[[repo]]
name = "x"
url = "https://example.com"
"#;
        let manifest: Manifest = toml::from_str(toml).unwrap();
        assert_eq!(
            manifest.settings.cache_dir,
            PathBuf::from(".repo-check-cache")
        );
        assert_eq!(manifest.settings.timeout_secs, 120);
    }

    #[test]
    fn duplicate_names_rejected() {
        let toml = r#"
[[repo]]
name = "dup"
url = "https://example.com/a"

[[repo]]
name = "dup"
url = "https://example.com/b"
"#;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.toml");
        std::fs::write(&path, toml).unwrap();
        let err = load_manifest(&path).unwrap_err();
        assert!(
            err.to_string().contains("duplicate"),
            "expected duplicate error, got: {err}"
        );
    }
}
