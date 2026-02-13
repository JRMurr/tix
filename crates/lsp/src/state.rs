// ==============================================================================
// AnalysisState: Salsa database + open file tracking
// ==============================================================================
//
// Wraps the Salsa RootDatabase and TypeAliasRegistry together with per-file
// cached analysis results. The LSP server holds this behind a Mutex because
// rnix::Root is !Send + !Sync and all analysis must run on a single thread
// (via spawn_blocking).

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use lang_ast::{
    module_and_source_maps, ExprId, Module, ModuleSourceMap, NameId, NameResolution, NixFile,
    RootDatabase,
};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::imports::resolve_imports;
use lang_check::{CheckResult, InferenceResult};

use crate::convert::LineIndex;

/// Cached analysis output for a single open file.
pub struct FileAnalysis {
    pub nix_file: NixFile,
    pub line_index: LineIndex,
    pub module: Module,
    pub source_map: ModuleSourceMap,
    pub name_res: NameResolution,
    pub check_result: CheckResult,
    /// Maps ExprIds of import sub-expressions (Apply, Reference, Literal)
    /// to the resolved target path. For jumping from `import ./foo.nix` to the file.
    pub import_targets: HashMap<ExprId, PathBuf>,
    /// Maps NameIds bound to import expressions to the target path.
    /// For jumping through Selects: `x.child` where `x = import ./foo.nix`.
    pub name_to_import: HashMap<NameId, PathBuf>,
}

impl FileAnalysis {
    pub fn inference(&self) -> Option<&InferenceResult> {
        self.check_result.inference.as_ref()
    }
}

/// All mutable state for the LSP's analysis pipeline.
pub struct AnalysisState {
    pub db: RootDatabase,
    pub registry: TypeAliasRegistry,
    /// Cached per-file analysis, keyed by the canonical path we give to Salsa.
    pub files: HashMap<PathBuf, FileAnalysis>,
}

impl AnalysisState {
    pub fn new(registry: TypeAliasRegistry) -> Self {
        Self {
            db: RootDatabase::default(),
            registry,
            files: HashMap::new(),
        }
    }

    /// Update file contents and re-run analysis. Returns the path key used
    /// for cache lookup (the same PathBuf passed in).
    pub fn update_file(&mut self, path: PathBuf, contents: String) -> &FileAnalysis {
        let line_index = LineIndex::new(&contents);
        let nix_file = self.db.set_file_contents(path.clone(), contents);

        let (module, source_map) = module_and_source_maps(&self.db, nix_file);
        let name_res = lang_ast::name_resolution(&self.db, nix_file);

        // Resolve literal imports before type-checking.
        let mut in_progress = HashSet::new();
        let mut cache = HashMap::new();
        let import_resolution = resolve_imports(
            &self.db,
            nix_file,
            &module,
            &name_res,
            &self.registry,
            &mut in_progress,
            &mut cache,
        );
        // TODO: surface import_resolution.errors as LSP diagnostics.

        let import_targets = import_resolution.targets;

        // Build name→import mapping: for each let-binding or attrset field
        // whose value expression is a resolved import, record the name→path link.
        // This powers Select-through-import navigation (e.g. `x.child` where
        // `x = import ./foo.nix` jumps to `child` in foo.nix).
        let grouped = lang_ast::group_def(&self.db, nix_file);
        let mut name_to_import = HashMap::new();
        for group in grouped.iter() {
            for typedef in group {
                if let Some(path) = import_targets.get(&typedef.expr()) {
                    name_to_import.insert(typedef.name(), path.clone());
                }
            }
        }

        let check_result = lang_check::check_file_collecting(
            &self.db,
            nix_file,
            &self.registry,
            import_resolution.types,
        );

        self.files.insert(
            path.clone(),
            FileAnalysis {
                nix_file,
                line_index,
                module,
                source_map,
                name_res,
                check_result,
                import_targets,
                name_to_import,
            },
        );

        self.files.get(&path).unwrap()
    }

    pub fn get_file(&self, path: &PathBuf) -> Option<&FileAnalysis> {
        self.files.get(path)
    }
}
