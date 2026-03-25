# Phase 4b: Partial Inference for typeof-Containing Type Exports

## Problem

When file A declares `/** type Scope = typeof scope; */` and file B does
`import("./a.nix").Scope`, the type import needs `scope`'s inferred type from
file A. But the coordinator infers files as whole units — there's no way to
get a single binding's type without running full inference.

If file A also imports file B (`import ./b.nix scope`), full inference of A
requires B, and B needs A's type exports — a cycle. But `scope`'s SCC doesn't
depend on B, so partial inference (just the early SCC groups) would break the
cycle.

## What Exists Already

### Phase 4a laid the groundwork

- `extract_type_exports(module) -> HashMap<SmolStr, ParsedTy>` extracts
  inline type alias declarations from a Module's doc comments
  (`lib.rs:55`).
- `CheckCtx.imported_type_exports: HashMap<PathBuf, HashMap<SmolStr, ParsedTy>>`
  holds resolved type exports from other files.
- `CheckCtx.with_imported_type_exports()` builder sets it.
- `intern_parsed_ty` handles `ImportType(path, name)` by looking up
  `imported_type_exports[resolved_path][name]` and calling
  `intern_fresh_ty` on the result (`lib.rs:~1350`).
- Tests wire this up manually — the coordinator does NOT populate these fields yet.

### Key infrastructure

- `infer_prog_partial` (`infer.rs:113`) already processes SCC groups in a
  loop and supports early exit (line 142, memory pressure). The loop is at
  line 139: `for (i, group) in groups.into_iter().enumerate()`.
- `InferenceResult.name_ty_map: ArenaMap<NameId, TyRef>` maps binding names
  to their canonicalized output types.
- `InferenceResult.arena: Arc<TypeArena>` holds the output types.
- `OwnedTy::new(arena, ty_ref).compact()` converts a TyRef into a
  self-contained portable type.
- `GroupedDefs = Vec<DependentGroup>` where `DependentGroup = Vec<TypeDef>`.
  Each `TypeDef` has `.name() -> NameId`. Groups are topologically ordered.
- `FileSlot` in coordinator uses `Computing`/`Ready` pattern with
  condvar for concurrent access.

### ParsedTy variants involved

- `ParsedTy::TypeOf(SmolStr)` — resolved in `intern_parsed_ty` via
  `poly_type_env` lookup.
- `ParsedTy::ImportType(String, SmolStr)` — resolved via
  `imported_type_exports`.

## Implementation Plan

### Step 1: `find_typeof_targets` — identify which bindings need partial inference

Add to `lib.rs` (near `extract_type_exports`):

```rust
/// For exported type aliases that contain `typeof varname`, return the
/// set of binding names that need to be inferred.
pub fn find_typeof_targets(
    exports: &HashMap<SmolStr, ParsedTy>,
) -> HashSet<SmolStr> {
    let mut targets = HashSet::new();
    for body in exports.values() {
        collect_typeof_names(body, &mut targets);
    }
    targets
}

fn collect_typeof_names(ty: &ParsedTy, out: &mut HashSet<SmolStr>) {
    match ty {
        ParsedTy::TypeOf(name) => { out.insert(name.clone()); }
        ParsedTy::Param(inner) | ParsedTy::Return(inner) => {
            collect_typeof_names(&inner.0, out);
        }
        ParsedTy::FieldAccess(inner, _) => {
            collect_typeof_names(&inner.0, out);
        }
        // Other variants don't contain typeof
        _ => {}
    }
}
```

### Step 2: `find_scc_group_for_name` — map binding name to SCC group index

Add to `lib.rs`:

```rust
/// Given a binding name and grouped defs, find the SCC group index
/// that contains the binding. Returns None if not found.
pub fn find_scc_group_for_name(
    module: &Module,
    groups: &GroupedDefs,
    name: &str,
) -> Option<usize> {
    for (i, group) in groups.iter().enumerate() {
        for def in group {
            if module[def.name()].text.as_str() == name {
                return Some(i);
            }
        }
    }
    None
}
```

### Step 3: `run_partial_inference` — infer up to a specific SCC group

Add to `lib.rs`:

```rust
/// Run inference on SCC groups 0..=stop_after_group only, skipping
/// infer_root and canonicalization. Returns the binding types for
/// the requested target names as OwnedTy values.
pub fn run_partial_inference(
    inputs: &InferenceInputs,
    stop_after_group: usize,
    target_names: &HashSet<SmolStr>,
) -> HashMap<SmolStr, OwnedTy> {
    let aliases = load_inline_aliases(Arc::clone(&inputs.registry), &inputs.module);

    let check = CheckCtx::new(
        &inputs.module,
        &inputs.name_res,
        &inputs.module_indices.binding_expr,
        aliases,
        inputs.import_types.clone(),
        Arc::clone(&inputs.context_args),
    );

    // Use infer_prog_up_to_group instead of infer_prog_partial
    let (result, _diagnostics) = check.infer_prog_up_to_group(
        inputs.grouped_defs.clone(),
        stop_after_group,
    );

    // Extract target binding types from the result
    let mut binding_types = HashMap::new();
    for (name_id, &ty_ref) in result.name_ty_map.iter() {
        let name_text = inputs.module[name_id].text.clone();
        if target_names.contains(name_text.as_str()) {
            binding_types.insert(
                name_text,
                OwnedTy::new(result.arena.clone(), ty_ref).compact(),
            );
        }
    }
    binding_types
}
```

### Step 4: `infer_prog_up_to_group` — the actual truncated inference

Add to `infer.rs` (mirrors `infer_prog_partial` but stops early and
skips canonicalization). Key differences from `infer_prog_partial`:

1. Takes `stop_after_group: usize` parameter
2. Loop breaks after `i > stop_after_group` (line 139 equivalent)
3. Does NOT call `infer_root()` (not needed for binding types)
4. Uses a simplified canonicalization that only processes the target
   names (not all expressions). Or: reuse the full Collector but only
   extract the needed names from the result.

```rust
/// Infer SCC groups 0..=stop_after_group only. Returns an
/// InferenceResult with name_ty_map populated for inferred bindings.
/// Skips infer_root and expr-level canonicalization.
pub fn infer_prog_up_to_group(
    mut self,
    groups: GroupedDefs,
    stop_after_group: usize,
) -> (InferenceResult, Vec<TixDiagnostic>) {
    // Pre-allocate TyIds (same as infer_prog_partial line 119-122)
    let len = self.module.names().len() + self.module.exprs().len();
    for _ in 0..len {
        self.new_var();
    }

    let mut errors = Vec::new();

    if let Some(err) = self.pre_apply_entry_lambda_annotations() {
        errors.push(err);
    }

    for (i, group) in groups.into_iter().enumerate() {
        if i > stop_after_group {
            break;
        }
        let group_errors = self.infer_scc_group(group);
        errors.extend(group_errors);
    }

    // Canonicalize only name types (skip expr types and infer_root)
    let diagnostics = diagnostic::errors_to_diagnostics(
        &errors, &self.types.storage, self.module
    );
    let mut collector = Collector::new(self);
    let result = collector.finalize_names_only();  // NEW: name-only canon
    (result, diagnostics)
}
```

**Alternative (simpler):** Just use the existing `finalize_inference()` in
Collector — it canonicalizes names too. The extra expr-level work is wasted
but correctness is preserved. If performance is a concern, add
`finalize_names_only()` later.

The simpler version:

```rust
pub fn infer_prog_up_to_group(
    mut self,
    groups: GroupedDefs,
    stop_after_group: usize,
) -> (InferenceResult, Vec<TixDiagnostic>) {
    let len = self.module.names().len() + self.module.exprs().len();
    for _ in 0..len { self.new_var(); }

    let mut errors = Vec::new();
    if let Some(err) = self.pre_apply_entry_lambda_annotations() {
        errors.push(err);
    }

    for (i, group) in groups.into_iter().enumerate() {
        if i > stop_after_group { break; }
        errors.extend(self.infer_scc_group(group));
    }

    errors.extend(std::mem::take(&mut self.deferred_errors));
    let warnings = std::mem::take(&mut self.warnings);
    let mut diagnostics = diagnostic::errors_to_diagnostics(
        &errors, &self.types.storage, self.module
    );
    diagnostics.extend(diagnostic::warnings_to_diagnostics(&warnings));

    let mut collector = Collector::new(self);
    let result = collector.finalize_inference();  // reuse existing
    (result, diagnostics)
}
```

### Step 5: `TypeExportSlot` — coordinator caching

Add to `coordinator.rs`:

```rust
/// State of a file's type exports in the coordinator cache.
enum TypeExportSlot {
    Computing { notify: Arc<(Mutex<bool>, Condvar)> },
    Ready(HashMap<SmolStr, ParsedTy>),
}
```

Add to `InferenceCoordinator`:

```rust
pub struct InferenceCoordinator {
    cache: DashMap<PathBuf, FileSlot>,
    type_export_cache: DashMap<PathBuf, TypeExportSlot>,  // NEW
    reverse_deps: Mutex<HashMap<PathBuf, HashSet<PathBuf>>>,
    forward_deps: Mutex<HashMap<PathBuf, Vec<PathBuf>>>,
}
```

### Step 6: `demand_type_exports` — the core method

Add to `InferenceCoordinator`:

```rust
pub fn demand_type_exports(
    &self,
    path: &Path,
    syntax_provider: &dyn SyntaxProvider,
) -> Option<HashMap<SmolStr, ParsedTy>> {
    // 1. Check cache
    if let Some(entry) = self.type_export_cache.get(path) {
        match &*entry {
            TypeExportSlot::Ready(exports) => return Some(exports.clone()),
            TypeExportSlot::Computing { notify } => {
                // Wait for computing thread
                let (lock, cvar) = &**notify;
                let mut done = lock.lock().unwrap();
                while !*done { done = cvar.wait(done).unwrap(); }
                drop(done);
                // Re-read
                return self.type_export_cache.get(path)
                    .and_then(|e| match &*e {
                        TypeExportSlot::Ready(exports) => Some(exports.clone()),
                        _ => None,
                    });
            }
        }
    }

    // 2. Parse file, extract raw type exports
    let bundle = syntax_provider.syntax_for_file(path)?;
    let raw_exports = extract_type_exports(&bundle.module);

    if raw_exports.is_empty() {
        self.type_export_cache.insert(
            path.to_path_buf(),
            TypeExportSlot::Ready(HashMap::new()),
        );
        return Some(HashMap::new());
    }

    // 3. Check if any exports contain typeof
    let typeof_targets = find_typeof_targets(&raw_exports);

    if typeof_targets.is_empty() {
        // Pure parse-level — no inference needed
        self.type_export_cache.insert(
            path.to_path_buf(),
            TypeExportSlot::Ready(raw_exports.clone()),
        );
        return Some(raw_exports);
    }

    // 4. Partial inference needed
    // Claim the Computing slot
    let notify = Arc::new((Mutex::new(false), Condvar::new()));
    self.type_export_cache.insert(
        path.to_path_buf(),
        TypeExportSlot::Computing { notify: notify.clone() },
    );

    // Find max SCC group index needed
    let max_group = typeof_targets.iter()
        .filter_map(|name| find_scc_group_for_name(
            &bundle.module, &bundle.grouped_defs, name
        ))
        .max()
        .unwrap_or(0);

    // Resolve imports for the partial inference (same as compute_file)
    let base_dir = path.parent().unwrap_or(Path::new("/"));
    let import_resolution = resolve_import_types(
        &bundle.module, &bundle.name_res, base_dir,
        |dep_path| {
            if let Some(sig) = self.get_signature(dep_path) {
                return Some(sig);
            }
            let dep_result = self.demand_file(dep_path, syntax_provider)?;
            dep_result.signature.map(|s| s.root_ty)
        },
        Some(&bundle.registry),
    );

    let inputs = InferenceInputs {
        module: bundle.module,
        module_indices: bundle.module_indices,
        name_res: bundle.name_res,
        grouped_defs: bundle.grouped_defs,
        registry: bundle.registry,
        import_types: import_resolution.types,
        import_diagnostics: vec![],  // not relevant for type exports
        context_args: bundle.context_args,
        rss_limit_mb: None,
        file_path: Some(path.to_path_buf()),
    };

    let binding_types = run_partial_inference(&inputs, max_group, &typeof_targets);

    // 5. Resolve typeof references in exports
    let mut resolved_exports = raw_exports;
    // For each export that contains TypeOf, replace with the inferred type.
    // This needs a resolve pass that substitutes TypeOf(name) with the
    // OwnedTy from binding_types. Since ParsedTy can't hold OwnedTy,
    // convert OwnedTy back to ParsedTy or use a different representation.
    //
    // SIMPLEST APPROACH: Don't try to resolve at the ParsedTy level.
    // Instead, when the consuming file hits ImportType("./a.nix", "Scope")
    // and Scope's body is TypeOf("scope"), the consuming file's
    // intern_parsed_ty resolves typeof by looking up binding_types.
    //
    // So store BOTH the raw ParsedTy exports AND the resolved binding
    // types. The consuming file's CheckCtx gets:
    //   imported_type_exports: the raw ParsedTy (may contain TypeOf)
    //   imported_typeof_bindings: HashMap<PathBuf, HashMap<SmolStr, OwnedTy>>
    //     for resolving TypeOf within imported type bodies.
    //
    // OR: simpler still — store the resolved exports as ParsedTy by
    // converting OwnedTy back to ParsedTy. This is lossy (generics become
    // TyVar(0)) but works for concrete types like { x: int }.

    // Signal completion
    let (lock, cvar) = &*notify;
    *lock.lock().unwrap() = true;
    cvar.notify_all();
    self.type_export_cache.insert(
        path.to_path_buf(),
        TypeExportSlot::Ready(resolved_exports.clone()),
    );

    Some(resolved_exports)
}
```

### Step 7: Wire into `compute_file`

In `coordinator.rs:compute_file`, after building `InferenceInputs` but
before `run_inference`, scan for cross-file type references in doc
comments and populate the CheckCtx fields:

```rust
// In compute_file, after import_resolution:

// Scan doc comments for import("path").TypeName references
let type_import_paths = scan_type_import_paths(&bundle.module);
let mut imported_type_exports = HashMap::new();
for dep_path in type_import_paths {
    let resolved = base_dir.join(&dep_path);
    if let Some(exports) = self.demand_type_exports(&resolved, syntax_provider) {
        imported_type_exports.insert(resolved, exports);
    }
}

// Scan for typeof import("path") references
let typeof_import_paths = scan_typeof_import_paths(&bundle.module);
let mut typeof_import_types = HashMap::new();
for dep_path in typeof_import_paths {
    let resolved = base_dir.join(&dep_path);
    if let Some(sig) = self.get_signature(&resolved) {
        typeof_import_types.insert(resolved, sig);
    } else if let Some(result) = self.demand_file(&resolved, syntax_provider) {
        if let Some(sig) = result.signature {
            typeof_import_types.insert(resolved, sig.root_ty);
        }
    }
}

// Add to InferenceInputs (needs new fields) or wire via CheckBuilder
```

### Step 8: `scan_type_import_paths` / `scan_typeof_import_paths`

Add to `imports.rs` (or a new `type_imports.rs`):

```rust
/// Scan a Module's doc comments for import("path").TypeName references.
/// Returns the set of file paths referenced.
pub fn scan_type_import_paths(module: &Module) -> HashSet<String> {
    let mut paths = HashSet::new();
    // Walk inline_type_aliases
    for alias_source in &module.inline_type_aliases {
        if let Some((_, body)) = comment_parser::parse_inline_type_alias(alias_source) {
            collect_import_paths(&body, &mut paths);
        }
    }
    // Walk all doc comment annotations in type_dec_map
    for (_, docs) in module.type_dec_map.all_docs() {
        for doc in docs {
            if let Ok(decls) = comment_parser::parse_and_collect(doc) {
                for decl in decls {
                    collect_import_paths(&decl.type_expr, &mut paths);
                }
            }
        }
    }
    paths
}

fn collect_import_paths(ty: &ParsedTy, out: &mut HashSet<String>) {
    match ty {
        ParsedTy::ImportType(path, _) => { out.insert(path.clone()); }
        ParsedTy::TypeOfImport(path) => { out.insert(path.clone()); }
        ParsedTy::Param(inner) | ParsedTy::Return(inner) => {
            collect_import_paths(&inner.0, out);
        }
        ParsedTy::FieldAccess(inner, _) => {
            collect_import_paths(&inner.0, out);
        }
        // Other variants don't contain import paths
        _ => {}
    }
}
```

Note: `module.type_dec_map.all_docs()` may not exist — check the actual
API. The doc comments are stored per-NameId in `ModuleTypeDecMap`. You may
need to iterate `module.names()` and call `type_dec_map.docs_for_name()`.

### Step 9: Wire `InferenceInputs` or `CheckBuilder`

Two options:

**Option A**: Add fields to `InferenceInputs`:
```rust
pub struct InferenceInputs {
    // ... existing fields ...
    pub imported_type_exports: HashMap<PathBuf, HashMap<SmolStr, ParsedTy>>,
    pub typeof_import_types: HashMap<PathBuf, OwnedTy>,
    pub file_base_dir: Option<PathBuf>,
}
```

Then in `CheckBuilder::run()`, pass these to CheckCtx via the existing
`with_*` methods.

**Option B**: Add builder methods to `CheckBuilder`:
```rust
impl CheckBuilder {
    pub fn imported_type_exports(mut self, ...) -> Self { ... }
    pub fn typeof_import_types(mut self, ...) -> Self { ... }
    pub fn file_base_dir(mut self, ...) -> Self { ... }
}
```

**Option A is cleaner** since InferenceInputs is the canonical bundle.

### Step 10: LSP integration

The LSP's `analyze_file` in `state.rs` also needs updating. It creates
InferenceInputs via the Salsa queries. The easiest approach: after
building InferenceInputs, scan for cross-file type references and populate
the new fields using the coordinator.

Check `lsp/src/state.rs` for `build_inference_inputs` or equivalent.

## Resolving TypeOf in Imported Type Bodies

The trickiest part: when file B imports `import("./a.nix").Scope` and
`Scope`'s body is `TypeOf("scope")`, the consuming file's `intern_fresh_ty`
needs to resolve that `TypeOf`. But the consuming file's `poly_type_env`
doesn't have `scope` — it's in file A.

**Solution**: Before interning `ImportType`, resolve any `TypeOf` in the
imported type body using file A's binding types. Add a
`resolve_typeof_in_imported_type` step:

```rust
// In intern_parsed_ty, ImportType case (lib.rs:~1350):
ParsedTy::ImportType(path, name) => {
    if let Some(base) = &self.file_base_dir {
        let resolved = base.join(path);
        if let Some(exports) = self.imported_type_exports.get(&resolved) {
            if let Some(alias_body) = exports.get(name.as_str()).cloned() {
                // If the body contains TypeOf, we need the binding
                // types from the exporting file to resolve them.
                // For now, try intern_fresh_ty — if it contains
                // TypeOf("scope") and scope is not in our poly_type_env,
                // it degrades to fresh var (existing behavior).
                //
                // With Phase 4b: the coordinator pre-resolves TypeOf
                // in exported types, so the body is already clean.
                return self.intern_fresh_ty(alias_body);
            }
        }
    }
    self.new_var()
}
```

The cleanest approach: `demand_type_exports` returns **fully resolved**
exports where `TypeOf("scope")` has been replaced with the actual type.
This means converting the partial inference's `OwnedTy` back to `ParsedTy`
(lossy but workable for concrete types), or storing a parallel map.

**Pragmatic approach**: Store both raw exports and a `typeof_resolutions`
map. The consuming file's `intern_parsed_ty` checks if the imported type
body contains `TypeOf`, and if so, looks up the resolution:

```rust
// New field on CheckCtx:
typeof_resolutions: HashMap<(PathBuf, SmolStr), OwnedTy>,
// Keyed by (source file path, binding name)

// In intern_parsed_ty, TypeOf case — extend to check typeof_resolutions
// when the typeof target isn't in our own poly_type_env:
ParsedTy::TypeOf(name) => {
    // First: try local poly_type_env (existing)
    // Second: try typeof_resolutions from imported files
    // (only relevant when processing an imported type body)
}
```

Actually, the simplest approach that avoids all this complexity:

**In `demand_type_exports`, after partial inference, replace TypeOf nodes
in the exported ParsedTy with the resolved primitive types.** Since we
know the binding's OwnedTy, we can pattern-match common cases:

```rust
fn resolve_export_typeof(
    body: &ParsedTy,
    binding_types: &HashMap<SmolStr, OwnedTy>,
) -> ParsedTy {
    match body {
        ParsedTy::TypeOf(name) => {
            if let Some(owned) = binding_types.get(name.as_str()) {
                owned_ty_to_parsed_ty(owned)  // lossy conversion
            } else {
                body.clone()
            }
        }
        ParsedTy::Param(inner) => {
            ParsedTy::Param(ParsedTyRef::from(
                resolve_export_typeof(&inner.0, binding_types)
            ))
        }
        // ... recurse for all variants ...
        _ => body.clone()
    }
}
```

`owned_ty_to_parsed_ty` converts `OwnedTy` (which holds `OutputTy` in a
`TypeArena`) back to `ParsedTy`. This is straightforward for concrete types:

```rust
fn owned_ty_to_parsed_ty(owned: &OwnedTy) -> ParsedTy {
    output_ty_to_parsed_ty(&owned.arena, owned.root)
}

fn output_ty_to_parsed_ty(arena: &TypeArena, ty_ref: TyRef) -> ParsedTy {
    match arena.resolve(ty_ref) {
        OutputTy::Primitive(p) => ParsedTy::Primitive(*p),
        OutputTy::TyVar(_) => ParsedTy::TyVar(TypeVarValue::Generic("a".into())),
        OutputTy::List(inner) => ParsedTy::List(
            ParsedTyRef::from(output_ty_to_parsed_ty(arena, *inner))
        ),
        OutputTy::Lambda { param, body } => ParsedTy::Lambda {
            param: ParsedTyRef::from(output_ty_to_parsed_ty(arena, *param)),
            body: ParsedTyRef::from(output_ty_to_parsed_ty(arena, *body)),
        },
        OutputTy::AttrSet(attr) => ParsedTy::AttrSet(AttrSetTy {
            fields: attr.fields.iter().map(|(k, v)| {
                (k.clone(), ParsedTyRef::from(output_ty_to_parsed_ty(arena, *v)))
            }).collect(),
            dyn_ty: attr.dyn_ty.map(|d| {
                ParsedTyRef::from(output_ty_to_parsed_ty(arena, d))
            }),
            open: attr.open,
            optional_fields: attr.optional_fields.clone(),
        }),
        OutputTy::Union(members) => ParsedTy::Union(
            members.iter().map(|m| {
                ParsedTyRef::from(output_ty_to_parsed_ty(arena, *m))
            }).collect()
        ),
        OutputTy::Intersection(members) => ParsedTy::Intersection(
            members.iter().map(|m| {
                ParsedTyRef::from(output_ty_to_parsed_ty(arena, *m))
            }).collect()
        ),
        OutputTy::Named(name, inner) => {
            // Preserve alias name
            output_ty_to_parsed_ty(arena, *inner)
        }
        OutputTy::Top => ParsedTy::Top,
        OutputTy::Bottom => ParsedTy::Bottom,
        OutputTy::Neg(_) => ParsedTy::Top, // approximation
    }
}
```

## Testing Strategy

### Unit tests (red-green TDD)

1. **Partial inference basic**: Create a CheckCtx, call
   `infer_prog_up_to_group(groups, 0)`, verify the first SCC group's
   bindings have types in the result.

2. **find_typeof_targets**: Parse `/** type Scope = typeof scope; */`,
   verify it returns `{"scope"}`.

3. **The motivating case** (multi-file):
   ```
   default.nix:
     let
       scope = { mkDerivation = x: x; };
       /** type Scope = typeof scope; */
       pkg = import ./package.nix scope;
     in pkg

   package.nix:
     /** type: args :: import("./default.nix").Scope */
     args: args.mkDerivation {}
   ```
   Verify package.nix sees `Scope` as `{ mkDerivation: a -> a }`.

4. **Genuine cycle**: scope depends on package.nix, package.nix imports
   Scope → error.

### PBT extension

Add to `pbt/type_ops.rs`:
- Generate random let bindings, export their type via `typeof`, import
  in another file. Verify roundtrip.

## File Summary

| File | Changes |
|------|---------|
| `lib.rs` | `find_typeof_targets()`, `find_scc_group_for_name()`, `run_partial_inference()`. New fields on `InferenceInputs`. |
| `infer.rs` | `infer_prog_up_to_group()` — truncated SCC loop |
| `coordinator.rs` | `TypeExportSlot`, `type_export_cache`, `demand_type_exports()`. Wire into `compute_file()`. |
| `imports.rs` | `scan_type_import_paths()`, `scan_typeof_import_paths()` |
| `aliases.rs` or new file | `owned_ty_to_parsed_ty()` conversion |
| `lsp/src/state.rs` | Populate new InferenceInputs fields during analysis |
| `tests.rs` | Multi-file tests for the motivating case + cycle detection |
| `pbt/type_ops.rs` | Cross-file typeof roundtrip property |

## Suggested Order

1. `find_typeof_targets` + `find_scc_group_for_name` (pure functions, easy to test)
2. `infer_prog_up_to_group` (mirror of existing code, add test)
3. `run_partial_inference` (wires 1+2 together)
4. `owned_ty_to_parsed_ty` (conversion function, test with known types)
5. `demand_type_exports` (coordinator method, uses 1-4)
6. `scan_type_import_paths` (doc comment scanning)
7. Wire into `compute_file` and `InferenceInputs`
8. LSP integration
9. Multi-file tests for the full flow
