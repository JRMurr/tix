mod check;
mod config;
mod gen_stubs;
mod init;

use std::collections::HashMap;
use std::{error::Error, path::PathBuf};

use clap::{Parser, Subcommand};
use lang_ast::{module_and_source_maps, name_resolution, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::check_file_collecting;
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use lang_check::imports::{import_errors_to_diagnostics, resolve_import_types_from_stubs};
use lang_ty::OutputTy;
use miette::{LabeledSpan, NamedSource};
use rowan::ast::AstNode;

// =============================================================================
// CLI Argument Parsing
// =============================================================================
//
// The CLI supports two modes:
//   1. Type-check mode (default): `tix-cli file.nix [--stubs ...]`
//   2. Subcommand mode: `tix-cli gen-stubs nixos [...]`
//
// Backward compatibility: bare `tix-cli file.nix` works because `file_path`
// is parsed when no subcommand matches.

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Path to the Nix file to type-check
    file_path: Option<PathBuf>,

    /// Paths to .tix stub files or directories (recursive)
    #[arg(long = "stubs", value_name = "PATH")]
    stub_paths: Vec<PathBuf>,

    /// Do not load the built-in nixpkgs stubs
    #[arg(long)]
    no_default_stubs: bool,

    /// Path to tix.toml config file (auto-discovered if not specified)
    #[arg(long = "config", value_name = "PATH")]
    config_path: Option<PathBuf>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Generate .tix stub files from external sources
    GenStubs {
        #[command(subcommand)]
        source: GenStubsSource,
    },

    /// Infer a Nix file's type and emit it as a .tix val declaration
    GenStub {
        /// Path to the Nix file to infer
        file_path: PathBuf,

        /// Paths to .tix stub files or directories (recursive)
        #[arg(long = "stubs", value_name = "PATH")]
        stub_paths: Vec<PathBuf>,

        /// Do not load the built-in nixpkgs stubs
        #[arg(long)]
        no_default_stubs: bool,

        /// Output file path (default: stdout)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Scaffold a tix.toml by scanning and classifying project files
    Init {
        /// Project directory (default: current directory)
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Write without asking for confirmation
        #[arg(long)]
        yes: bool,

        /// Print what would be generated without writing
        #[arg(long)]
        dry_run: bool,
    },

    /// Type-check all files in a project using tix.toml configuration
    Check {
        /// Path to tix.toml config file (auto-discovered if not specified)
        #[arg(long = "config", value_name = "PATH")]
        config_path: Option<PathBuf>,

        /// Do not load the built-in nixpkgs stubs
        #[arg(long)]
        no_default_stubs: bool,

        /// Print file classifications
        #[arg(long)]
        verbose: bool,
    },

    /// Verify that a .tix stub matches the inferred type of a Nix file
    VerifyStubs {
        /// Path to the Nix file to verify
        file_path: PathBuf,

        /// Path to the .tix stub file to verify against
        #[arg(long = "stub")]
        stub_path: PathBuf,

        /// Additional stub paths or directories for import resolution
        #[arg(long = "stubs", value_name = "PATH")]
        extra_stubs: Vec<PathBuf>,

        /// Do not load the built-in nixpkgs stubs
        #[arg(long)]
        no_default_stubs: bool,
    },
}

/// Shared CLI arguments for all gen-stubs subcommands.
#[derive(clap::Args, Debug)]
struct CommonGenStubsArgs {
    /// Path to nixpkgs (default: <nixpkgs> from NIX_PATH)
    #[arg(long)]
    nixpkgs: Option<PathBuf>,

    /// Path to a flake directory (evaluates configurations)
    #[arg(long)]
    flake: Option<PathBuf>,

    /// Read pre-computed option tree JSON instead of running nix eval
    #[arg(long)]
    from_json: Option<PathBuf>,

    /// Output file path (default: stdout)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Maximum depth for recursive option tree walking
    #[arg(long, default_value = "8")]
    max_depth: u32,

    /// Include option descriptions as ## doc comments in the output
    #[arg(long)]
    descriptions: bool,
}

impl From<CommonGenStubsArgs> for gen_stubs::CommonOptions {
    fn from(args: CommonGenStubsArgs) -> Self {
        Self {
            nixpkgs: args.nixpkgs,
            flake: args.flake,
            from_json: args.from_json,
            output: args.output,
            max_depth: args.max_depth,
            descriptions: args.descriptions,
        }
    }
}

#[derive(Subcommand, Debug)]
enum GenStubsSource {
    /// Generate stubs from NixOS option declarations
    Nixos {
        #[command(flatten)]
        common: CommonGenStubsArgs,

        /// Hostname to select from nixosConfigurations (required if flake has multiple)
        #[arg(long)]
        hostname: Option<String>,
    },

    /// Generate stubs from Home Manager option declarations
    HomeManager {
        #[command(flatten)]
        common: CommonGenStubsArgs,

        /// Path to home-manager source (default: flake registry)
        #[arg(long)]
        home_manager: Option<PathBuf>,

        /// Username to select from homeConfigurations (required if flake has multiple)
        #[arg(long)]
        username: Option<String>,
    },

    /// Generate val declarations for nixpkgs packages
    Pkgs {
        /// Path to nixpkgs (default: <nixpkgs> from NIX_PATH)
        #[arg(long)]
        nixpkgs: Option<PathBuf>,

        /// Read pre-computed classification JSON instead of running nix eval
        #[arg(long)]
        from_json: Option<PathBuf>,

        /// Output file path (default: stdout)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Maximum depth for recursing into sub-package-sets like llvmPackages,
        /// python3Packages, etc. (0 = flat, default: 1)
        #[arg(long, default_value = "1")]
        max_depth: u32,
    },
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();

    match args.command {
        Some(Command::Init { path, yes, dry_run }) => init::run_init(path, yes, dry_run),
        Some(Command::Check {
            config_path,
            no_default_stubs,
            verbose,
        }) => check::run_check_project(config_path, no_default_stubs, verbose),
        Some(Command::GenStubs { source }) => run_gen_stubs(source),
        Some(Command::GenStub {
            file_path,
            stub_paths,
            no_default_stubs,
            output,
        }) => run_gen_stub(file_path, stub_paths, no_default_stubs, output),
        Some(Command::VerifyStubs {
            file_path,
            stub_path,
            extra_stubs,
            no_default_stubs,
        }) => {
            let mismatches = run_verify_stubs(
                file_path.clone(),
                stub_path.clone(),
                extra_stubs,
                no_default_stubs,
            )?;
            if mismatches.is_empty() {
                println!(
                    "OK: {} matches {}",
                    file_path.display(),
                    stub_path.display()
                );
            } else {
                for mismatch in &mismatches {
                    let report = miette::Report::new_boxed(Box::new(
                        miette::MietteDiagnostic::new(format!(
                            "type mismatch for `{}`",
                            mismatch.val_name
                        ))
                        .with_labels(vec![miette::LabeledSpan::at(
                            mismatch.span,
                            "declared here",
                        )])
                        .with_help(format!("inferred type: {}", mismatch.inferred)),
                    ))
                    .with_source_code(mismatch.src.clone());
                    eprintln!("{:?}", report);
                }
                std::process::exit(1);
            }
            Ok(())
        }
        None => {
            let file_path = args.file_path.ok_or(
                "No file path provided. Usage: tix-cli <file.nix> or tix-cli gen-stubs <source>",
            )?;
            run_check(
                file_path,
                args.stub_paths,
                args.no_default_stubs,
                args.config_path,
            )
        }
    }
}

// =============================================================================
// gen-stubs dispatch
// =============================================================================

fn run_gen_stubs(source: GenStubsSource) -> Result<(), Box<dyn Error>> {
    match source {
        GenStubsSource::Nixos { common, hostname } => {
            gen_stubs::run_nixos(gen_stubs::NixosOptions {
                common: common.into(),
                hostname,
            })
        }
        GenStubsSource::HomeManager {
            common,
            home_manager,
            username,
        } => gen_stubs::run_home_manager(gen_stubs::HomeManagerOptions {
            common: common.into(),
            home_manager,
            username,
        }),
        GenStubsSource::Pkgs {
            nixpkgs,
            from_json,
            output,
            max_depth,
        } => gen_stubs::run_pkgs(gen_stubs::PkgsOptions {
            nixpkgs,
            from_json,
            output,
            max_depth,
        }),
    }
}

// =============================================================================
// gen-stub: infer a file and emit its type as a .tix declaration
// =============================================================================

fn run_gen_stub(
    file_path: PathBuf,
    stub_paths: Vec<PathBuf>,
    no_default_stubs: bool,
    output: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    let registry = build_registry(no_default_stubs, &stub_paths)?;

    let db: RootDatabase = Default::default();
    let file = db.read_file(file_path.clone())?;

    let (module, _source_map) = lang_ast::module_and_source_maps(&db, file);
    let name_res = lang_ast::name_resolution(&db, file);
    let base_dir = file_path.parent().unwrap_or(std::path::Path::new("/"));

    // Infer with stubs-only (no ephemeral stubs for gen-stub).
    let import_resolution =
        resolve_import_types_from_stubs(&module, &name_res, base_dir, &HashMap::new());

    let result = lang_check::check_file_collecting(
        &db,
        file,
        &registry,
        import_resolution.types,
        HashMap::new(),
    );

    let root_ty = result
        .inference
        .as_ref()
        .and_then(|inf| inf.expr_ty_map.get(module.entry_expr))
        .cloned()
        .ok_or("Failed to infer root type for file")?;

    // Format as a .tix val declaration.
    // Use the file stem as the declaration name, or "_" as a placeholder.
    let decl_name = file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("_");

    let root_ty_str = format!("{root_ty}");
    let tix_output = format!("val {decl_name} :: {root_ty_str};\n");

    match output {
        Some(path) => {
            std::fs::write(&path, &tix_output)?;
            eprintln!("Wrote stub to {}", path.display());
        }
        None => print!("{tix_output}"),
    }

    // Warn about types that may not round-trip through .tix parsing.
    if root_ty_str.contains('~') {
        eprintln!(
            "Warning: output contains negation types (~) which are not expressible in .tix syntax"
        );
    }

    Ok(())
}

// =============================================================================
// verify-stubs: check that a .tix stub matches the inferred type
// =============================================================================

/// A single type mismatch between a val declaration and inferred type.
/// Fields are used to build miette diagnostics in the VerifyStubs command handler.
#[derive(Debug)]
struct VerifyMismatch {
    val_name: String,
    inferred: String,
    src: NamedSource<String>,
    span: miette::SourceSpan,
}

/// Errors from verify-stubs that prevent verification from running.
#[derive(Debug, thiserror::Error)]
enum VerifyStubsError {
    #[error("reading {path}: {source}")]
    Io {
        path: PathBuf,
        source: std::io::Error,
    },

    #[error("parsing stub {path}: {message}")]
    StubParse { path: PathBuf, message: String },

    #[error("building registry: {0}")]
    Registry(String),

    #[error("inference failed: no root type for {path}")]
    NoRootType { path: PathBuf },
}

fn run_verify_stubs(
    file_path: PathBuf,
    stub_path: PathBuf,
    extra_stubs: Vec<PathBuf>,
    no_default_stubs: bool,
) -> Result<Vec<VerifyMismatch>, VerifyStubsError> {
    // Load stubs (including the one being verified). We append stub_path
    // to the extra stubs so build_registry loads everything in one pass.
    let mut all_stubs = extra_stubs;
    all_stubs.push(stub_path.clone());
    let registry = build_registry(no_default_stubs, &all_stubs)
        .map_err(|e| VerifyStubsError::Registry(e.to_string()))?;

    // Parse the stub file to get declared val types.
    let stub_source = std::fs::read_to_string(&stub_path).map_err(|e| VerifyStubsError::Io {
        path: stub_path.clone(),
        source: e,
    })?;
    let stub_file =
        comment_parser::parse_tix_file(&stub_source).map_err(|e| VerifyStubsError::StubParse {
            path: stub_path.clone(),
            message: e.to_string(),
        })?;

    let val_decls: Vec<_> = stub_file
        .declarations
        .iter()
        .filter_map(|d| match d {
            comment_parser::TixDeclaration::ValDecl { name, ty, span, .. } => {
                Some((name, ty, span))
            }
            _ => None,
        })
        .collect();

    if val_decls.is_empty() {
        eprintln!(
            "Warning: {} contains no val declarations to verify",
            stub_path.display()
        );
        return Ok(vec![]);
    }

    // Infer the Nix file.
    let db: RootDatabase = Default::default();
    let file = db
        .read_file(file_path.clone())
        .map_err(|e| VerifyStubsError::Io {
            path: file_path.clone(),
            source: e,
        })?;

    let (module, _source_map) = lang_ast::module_and_source_maps(&db, file);
    let name_res = lang_ast::name_resolution(&db, file);
    let base_dir = file_path.parent().unwrap_or(std::path::Path::new("/"));

    let import_resolution =
        resolve_import_types_from_stubs(&module, &name_res, base_dir, &HashMap::new());

    let result = lang_check::check_file_collecting(
        &db,
        file,
        &registry,
        import_resolution.types,
        HashMap::new(),
    );

    let root_ty = result
        .inference
        .as_ref()
        .and_then(|inf| inf.expr_ty_map.get(module.entry_expr))
        .cloned()
        .ok_or(VerifyStubsError::NoRootType {
            path: file_path.clone(),
        })?;

    // Compare each declared val against the inferred root type.
    // For a typical single-file stub with one val, this checks the root type.
    let stub_filename = stub_path.display().to_string();
    let mut mismatches = Vec::new();

    for (name, declared_ty, &(span_start, span_end)) in &val_decls {
        let declared_output = parsed_ty_to_output_ty(declared_ty, &registry, 0);
        let mut diffs = Vec::new();
        compare_types(
            &root_ty,
            &declared_output,
            &format!("val {name}"),
            &mut diffs,
        );
        if !diffs.is_empty() {
            mismatches.push(VerifyMismatch {
                val_name: name.to_string(),
                inferred: format!("{root_ty}"),
                src: NamedSource::new(stub_filename.clone(), stub_source.clone()),
                span: (span_start, span_end - span_start).into(),
            });
        }
    }

    Ok(mismatches)
}

use lang_check::aliases::parsed_ty_to_output_ty;

/// Structural comparison of inferred vs declared types. Reports mismatches
/// as human-readable strings. This is a best-effort check — it catches
/// missing fields, type kind mismatches, and primitive type mismatches.
/// Type variables in the stub are treated as wildcards (match anything).
fn compare_types(
    inferred: &OutputTy,
    declared: &OutputTy,
    path: &str,
    mismatches: &mut Vec<String>,
) {
    // Type variables in the declared type are wildcards — any inferred type matches.
    if matches!(declared, OutputTy::TyVar(_) | OutputTy::Top) {
        return;
    }

    match (inferred, declared) {
        // Attrset comparison: check that all declared fields exist with compatible types.
        (OutputTy::AttrSet(inf_attr), OutputTy::AttrSet(decl_attr)) => {
            for (field_name, decl_field_ty) in &decl_attr.fields {
                match inf_attr.fields.get(field_name) {
                    Some(inf_field_ty) => {
                        compare_types(
                            &inf_field_ty.0,
                            &decl_field_ty.0,
                            &format!("{path}.{field_name}"),
                            mismatches,
                        );
                    }
                    None => {
                        mismatches.push(format!(
                            "{path}: stub declares field `{field_name}` but implementation doesn't export it"
                        ));
                    }
                }
            }
        }

        // Lambda comparison: check param and body.
        (
            OutputTy::Lambda {
                param: inf_p,
                body: inf_b,
            },
            OutputTy::Lambda {
                param: decl_p,
                body: decl_b,
            },
        ) => {
            compare_types(&inf_p.0, &decl_p.0, &format!("{path} (param)"), mismatches);
            compare_types(&inf_b.0, &decl_b.0, &format!("{path} (return)"), mismatches);
        }

        // List comparison.
        (OutputTy::List(inf_inner), OutputTy::List(decl_inner)) => {
            compare_types(
                &inf_inner.0,
                &decl_inner.0,
                &format!("{path} (list element)"),
                mismatches,
            );
        }

        // Primitive exact match.
        (OutputTy::Primitive(a), OutputTy::Primitive(b)) if a == b => {}

        // Union comparison: each declared member must be compatible with at
        // least one inferred member (or the whole inferred type if it isn't a union).
        (OutputTy::Union(inf_members), OutputTy::Union(decl_members)) => {
            for decl_m in decl_members {
                let mut member_mismatches = Vec::new();
                let mut any_match = false;
                for inf_m in inf_members {
                    let mut trial = Vec::new();
                    compare_types(&inf_m.0, &decl_m.0, path, &mut trial);
                    if trial.is_empty() {
                        any_match = true;
                        break;
                    }
                    member_mismatches.extend(trial);
                }
                if !any_match {
                    mismatches.push(format!(
                        "{path}: stub declares union member `{}` but no matching inferred member found",
                        decl_m.0
                    ));
                }
            }
        }

        // Intersection comparison: each declared member must be compatible
        // with the inferred type.
        (_, OutputTy::Intersection(decl_members)) => {
            for decl_m in decl_members {
                compare_types(inferred, &decl_m.0, path, mismatches);
            }
        }
        (OutputTy::Intersection(inf_members), _) => {
            // If inferred is an intersection, any member matching suffices.
            let mut any_match = false;
            for inf_m in inf_members {
                let mut trial = Vec::new();
                compare_types(&inf_m.0, declared, path, &mut trial);
                if trial.is_empty() {
                    any_match = true;
                    break;
                }
            }
            if !any_match {
                mismatches.push(format!(
                    "{path}: stub declares `{declared}` but implementation infers `{inferred}`"
                ));
            }
        }

        // Single inferred type vs declared union: inferred must match at least
        // one declared member.
        (_, OutputTy::Union(decl_members)) => {
            let mut any_match = false;
            for decl_m in decl_members {
                let mut trial = Vec::new();
                compare_types(inferred, &decl_m.0, path, &mut trial);
                if trial.is_empty() {
                    any_match = true;
                    break;
                }
            }
            if !any_match {
                mismatches.push(format!(
                    "{path}: stub declares `{declared}` but implementation infers `{inferred}`"
                ));
            }
        }

        // Named types: unwrap and compare inner.
        (OutputTy::Named(_, inf_inner), _) => {
            compare_types(&inf_inner.0, declared, path, mismatches);
        }
        (_, OutputTy::Named(_, decl_inner)) => {
            compare_types(inferred, &decl_inner.0, path, mismatches);
        }

        // Type kind mismatch.
        _ => {
            mismatches.push(format!(
                "{path}: stub declares `{declared}` but implementation infers `{inferred}`"
            ));
        }
    }
}

// =============================================================================
// Type-check mode (original behavior)
// =============================================================================

fn run_check(
    file_path: PathBuf,
    stub_paths: Vec<PathBuf>,
    no_default_stubs: bool,
    config_path: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    let mut registry = build_registry(no_default_stubs, &stub_paths)?;

    // Discover or load tix.toml configuration.
    let canonical_path = std::fs::canonicalize(&file_path).unwrap_or(file_path.clone());
    let (toml_config, config_dir) = match &config_path {
        Some(explicit_path) => {
            let cfg = config::load_config(explicit_path)?;
            // Canonicalize the config directory so strip_prefix works against
            // the canonicalized file path (both must be absolute).
            let raw_dir = explicit_path.parent().unwrap_or(std::path::Path::new("."));
            let dir = std::fs::canonicalize(raw_dir).unwrap_or(raw_dir.to_path_buf());
            (Some(cfg), Some(dir))
        }
        None => {
            // Walk up from the file's parent directory looking for tix.toml.
            let start_dir = canonical_path.parent().unwrap_or(std::path::Path::new("."));
            match config::find_config(start_dir) {
                Some(found_config_path) => {
                    let dir = found_config_path
                        .parent()
                        .unwrap_or(std::path::Path::new("."))
                        .to_path_buf();
                    match config::load_config(&found_config_path) {
                        Ok(cfg) => (Some(cfg), Some(dir)),
                        Err(e) => {
                            eprintln!(
                                "Warning: failed to load {}: {e}",
                                found_config_path.display()
                            );
                            (None, None)
                        }
                    }
                }
                None => (None, None),
            }
        }
    };

    // Load additional stubs from tix.toml config.
    if let (Some(ref cfg), Some(ref dir)) = (&toml_config, &config_dir) {
        for stub in &cfg.stubs {
            let stub_path = dir.join(stub);
            if let Err(e) = load_stubs(&mut registry, &stub_path) {
                eprintln!(
                    "Warning: failed to load config stub '{}': {e}",
                    stub_path.display()
                );
            }
        }
    }

    if let Err(cycles) = registry.validate() {
        eprintln!("Error: cyclic type aliases detected: {:?}", cycles);
        std::process::exit(1);
    }

    // Resolve context args for this file based on tix.toml context definitions.
    let context_args = if let (Some(ref cfg), Some(ref dir)) = (&toml_config, &config_dir) {
        config::resolve_context_for_file(&canonical_path, cfg, dir, &mut registry).unwrap_or_else(
            |e| {
                eprintln!("Warning: failed to resolve context: {e}");
                HashMap::new()
            },
        )
    } else {
        HashMap::new()
    };

    let db: RootDatabase = Default::default();

    let file = db.read_file(file_path.clone())?;

    let (module, source_map) = module_and_source_maps(&db, file);
    let name_res = name_resolution(&db, file);
    let base_dir = file_path.parent().unwrap_or(std::path::Path::new("/"));

    // CLI uses stubs-only model: no recursive import inference. Imports
    // without stubs default to ⊤ (generic import :: a -> b). Users add
    // .tix stubs for more precision.
    let import_resolution =
        resolve_import_types_from_stubs(&module, &name_res, base_dir, &HashMap::new());

    let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);

    let mut result =
        check_file_collecting(&db, file, &registry, import_resolution.types, context_args);

    // Merge import diagnostics into the check result.
    result.diagnostics.extend(import_diagnostics);

    // If inference timed out, identify which bindings are incomplete
    // and include them in the diagnostic for actionable feedback.
    if result.timed_out {
        let missing_bindings: Vec<smol_str::SmolStr> = module
            .names()
            .filter(|(_, name)| {
                matches!(
                    name.kind,
                    lang_ast::NameKind::LetIn
                        | lang_ast::NameKind::RecAttrset
                        | lang_ast::NameKind::PlainAttrset
                )
            })
            .filter(|(id, _)| {
                result
                    .inference
                    .as_ref()
                    .is_none_or(|inf| inf.name_ty_map.get(*id).is_none())
            })
            .map(|(_, name)| name.text.clone())
            .collect();
        result.diagnostics.push(TixDiagnostic {
            at_expr: module.entry_expr,
            kind: TixDiagnosticKind::InferenceTimeout { missing_bindings },
        });
    }

    // Render diagnostics with miette for source context.
    let source_text = std::fs::read_to_string(&file_path)?;
    let (error_count, _warning_count) =
        render_diagnostics(&file_path, &source_text, &result.diagnostics, &source_map);

    if error_count > 0 {
        std::process::exit(1);
    }

    // If inference succeeded, print binding types and root type.
    if let Some(inference) = &result.inference {
        // Print per-name types (the let-bindings, function params, etc.).
        // Deduplicate by name text since the same name can appear multiple times
        // (e.g. a lambda pattern field `config` and a return attrset key `config`).
        // Prefer definitions (PatField, Param, LetIn) over PlainAttrset keys,
        // then prefer types without unions/intersections (cleaner early-canonical form).
        let mut seen = std::collections::BTreeMap::<String, (lang_ast::NameKind, OutputTy)>::new();
        for (name_id, name) in module.names() {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                seen.entry(name.text.to_string())
                    .and_modify(|(existing_kind, existing_ty)| {
                        // Prefer definitions over plain attrset keys.
                        if !existing_kind.is_definition() && name.kind.is_definition() {
                            *existing_kind = name.kind;
                            *existing_ty = ty.clone();
                        } else if existing_kind.is_definition() && !name.kind.is_definition() {
                            // Keep the existing definition type.
                        } else if ty.contains_union_or_intersection()
                            && !existing_ty.contains_union_or_intersection()
                        {
                            // Keep the existing (cleaner) one.
                        } else if !ty.contains_union_or_intersection()
                            && existing_ty.contains_union_or_intersection()
                        {
                            *existing_kind = name.kind;
                            *existing_ty = ty.clone();
                        }
                    })
                    .or_insert((name.kind, ty.clone()));
            }
        }

        println!("Bindings:");
        for (name, (_kind, ty)) in &seen {
            println!("  {name} :: {ty}");
        }

        // Print the root expression type.
        match inference.expr_ty_map.get(module.entry_expr) {
            Some(root_ty) => println!("\nRoot type:\n  {root_ty}"),
            None => {
                eprintln!("error: could not infer type for root expression");
                std::process::exit(1);
            }
        }
    }

    Ok(())
}

// =============================================================================
// Shared diagnostic rendering
// =============================================================================

/// Render diagnostics for a single file. Returns `(error_count, warning_count)`.
fn render_diagnostics(
    file_path: &std::path::Path,
    source_text: &str,
    diagnostics: &[TixDiagnostic],
    source_map: &lang_ast::ModuleSourceMap,
) -> (usize, usize) {
    let filename = file_path.display().to_string();
    let root = rnix::Root::parse(source_text).tree();
    let mut error_count = 0;
    let mut warning_count = 0;

    for diag in diagnostics {
        let is_warning = matches!(
            diag.kind,
            TixDiagnosticKind::UnresolvedName { .. }
                | TixDiagnosticKind::AnnotationArityMismatch { .. }
                | TixDiagnosticKind::AnnotationUnchecked { .. }
                | TixDiagnosticKind::DuplicateKey { .. }
                | TixDiagnosticKind::ImportNotFound { .. }
                | TixDiagnosticKind::InferenceTimeout { .. }
        );
        if is_warning {
            warning_count += 1;
        } else {
            error_count += 1;
        }

        // DuplicateKey carries its own AstPtr spans; other diagnostics
        // resolve ExprId → source span via the ModuleSourceMap.
        let labels = if let TixDiagnosticKind::DuplicateKey { first, second, .. } = &diag.kind {
            let to_span = |ptr: &lang_ast::AstPtr| {
                let node = ptr.to_node(root.syntax());
                let range = node.text_range();
                let start: usize = range.start().into();
                let len: usize = range.len().into();
                (start, len)
            };
            let (s1, l1) = to_span(first);
            let (s2, l2) = to_span(second);
            vec![
                LabeledSpan::at(s1..s1 + l1, "first defined here"),
                LabeledSpan::at(s2..s2 + l2, "duplicate defined here"),
            ]
        } else {
            let span = source_map.node_for_expr(diag.at_expr).map(|ptr| {
                let node = ptr.to_node(root.syntax());
                let range = node.text_range();
                let start: usize = range.start().into();
                let len: usize = range.len().into();
                (start, len)
            });
            span.map(|(offset, len)| vec![LabeledSpan::at(offset..offset + len, "here")])
                .unwrap_or_default()
        };

        // Build help text for MissingField suggestions.
        let help = match &diag.kind {
            TixDiagnosticKind::MissingField {
                suggestion: Some(s),
                ..
            } => Some(format!("did you mean `{s}`?")),
            _ => None,
        };

        let mut builder = miette::MietteDiagnostic::new(diag.kind.to_string());
        if !labels.is_empty() {
            builder = builder.with_labels(labels);
        }
        if let Some(help_text) = help {
            builder = builder.with_help(help_text);
        }
        if is_warning {
            builder = builder.with_severity(miette::Severity::Warning);
        }

        let report = miette::Report::new(builder)
            .with_source_code(NamedSource::new(filename.clone(), source_text.to_string()));
        eprintln!("{:?}", report);
    }

    (error_count, warning_count)
}

/// Build a TypeAliasRegistry from CLI flags, loading stubs and validating.
/// This consolidates the repeated registry setup across run_check, run_gen_stub,
/// and run_verify_stubs.
fn build_registry(
    no_default_stubs: bool,
    stub_paths: &[PathBuf],
) -> Result<TypeAliasRegistry, Box<dyn Error>> {
    let mut registry = if no_default_stubs {
        TypeAliasRegistry::new()
    } else {
        TypeAliasRegistry::with_builtins()
    };

    if let Ok(dir) = std::env::var("TIX_BUILTIN_STUBS") {
        registry.set_builtin_stubs_dir(PathBuf::from(dir));
    }

    for stub_path in stub_paths {
        load_stubs(&mut registry, stub_path)?;
    }

    if let Err(cycles) = registry.validate() {
        eprintln!("Error: cyclic type aliases detected: {:?}", cycles);
        std::process::exit(1);
    }

    Ok(registry)
}

/// Load .tix files from a path. If the path is a file, load it directly.
/// If it's a directory, recursively find all .tix files and load them.
fn load_stubs(registry: &mut TypeAliasRegistry, path: &PathBuf) -> Result<(), Box<dyn Error>> {
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                load_stubs(registry, &entry_path)?;
            } else if entry_path.extension().is_some_and(|ext| ext == "tix") {
                load_single_stub(registry, &entry_path)?;
            }
        }
    } else {
        load_single_stub(registry, path)?;
    }
    Ok(())
}

fn load_single_stub(
    registry: &mut TypeAliasRegistry,
    path: &PathBuf,
) -> Result<(), Box<dyn Error>> {
    let source = std::fs::read_to_string(path)?;
    let file = comment_parser::parse_tix_file(&source)
        .map_err(|e| format!("Error parsing {}: {}", path.display(), e))?;
    registry.load_tix_file(&file);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_ty::{AttrSetTy, PrimitiveTy, TyRef};

    fn oty_int() -> OutputTy {
        OutputTy::Primitive(PrimitiveTy::Int)
    }

    fn oty_string() -> OutputTy {
        OutputTy::Primitive(PrimitiveTy::String)
    }

    // =========================================================================
    // compare_types tests
    // =========================================================================

    #[test]
    fn compare_types_same_primitive_ok() {
        let mut m = Vec::new();
        compare_types(&oty_int(), &oty_int(), "root", &mut m);
        assert!(m.is_empty(), "same primitives should match");
    }

    #[test]
    fn compare_types_different_primitive_mismatch() {
        let mut m = Vec::new();
        compare_types(&oty_int(), &oty_string(), "root", &mut m);
        assert_eq!(m.len(), 1, "different primitives should mismatch");
        assert!(m[0].contains("root"));
    }

    #[test]
    fn compare_types_tyvar_declared_is_wildcard() {
        let mut m = Vec::new();
        compare_types(&oty_int(), &OutputTy::TyVar(0), "root", &mut m);
        assert!(m.is_empty(), "TyVar in declared should match anything");
    }

    #[test]
    fn compare_types_top_declared_is_wildcard() {
        let mut m = Vec::new();
        compare_types(&oty_int(), &OutputTy::Top, "root", &mut m);
        assert!(m.is_empty(), "Top in declared should match anything");
    }

    #[test]
    fn compare_types_attrset_missing_field() {
        let inf = OutputTy::AttrSet(AttrSetTy {
            fields: std::collections::BTreeMap::new(),
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        });
        let mut decl_fields = std::collections::BTreeMap::new();
        decl_fields.insert(smol_str::SmolStr::from("x"), TyRef::from(oty_int()));
        let decl = OutputTy::AttrSet(AttrSetTy {
            fields: decl_fields,
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        });
        let mut m = Vec::new();
        compare_types(&inf, &decl, "root", &mut m);
        assert_eq!(m.len(), 1, "missing field should produce mismatch");
        assert!(m[0].contains("x"));
    }

    #[test]
    fn compare_types_union_match() {
        let inf = OutputTy::Union(vec![TyRef::from(oty_int()), TyRef::from(oty_string())]);
        let decl = OutputTy::Union(vec![TyRef::from(oty_int()), TyRef::from(oty_string())]);
        let mut m = Vec::new();
        compare_types(&inf, &decl, "root", &mut m);
        assert!(m.is_empty(), "matching unions should be compatible");
    }

    #[test]
    fn compare_types_union_mismatch() {
        let inf = OutputTy::Union(vec![TyRef::from(oty_int())]);
        let decl = OutputTy::Union(vec![TyRef::from(oty_string())]);
        let mut m = Vec::new();
        compare_types(&inf, &decl, "root", &mut m);
        assert!(!m.is_empty(), "non-matching unions should mismatch");
    }

    #[test]
    fn compare_types_intersection_declared() {
        let inf = oty_int();
        let decl = OutputTy::Intersection(vec![TyRef::from(oty_int())]);
        let mut m = Vec::new();
        compare_types(&inf, &decl, "root", &mut m);
        assert!(
            m.is_empty(),
            "inferred matching all intersection members should pass"
        );
    }

    #[test]
    fn compare_types_lambda_match() {
        let inf = OutputTy::Lambda {
            param: TyRef::from(oty_int()),
            body: TyRef::from(oty_string()),
        };
        let decl = OutputTy::Lambda {
            param: TyRef::from(oty_int()),
            body: TyRef::from(oty_string()),
        };
        let mut m = Vec::new();
        compare_types(&inf, &decl, "root", &mut m);
        assert!(m.is_empty(), "matching lambdas should be compatible");
    }

    // =========================================================================
    // gen-stub / verify-stubs integration tests
    // =========================================================================

    #[test]
    fn gen_stub_produces_valid_tix() {
        // Type-check a simple file and generate a stub, then verify it parses.
        let dir = tempfile::tempdir().expect("create temp dir");
        let nix_path = dir.path().join("test.nix");
        let stub_path = dir.path().join("test.tix");
        std::fs::write(&nix_path, "let x = 1; in x").expect("write nix file");

        let result = run_gen_stub(nix_path, vec![], false, Some(stub_path.clone()));
        assert!(
            result.is_ok(),
            "gen-stub should succeed: {:?}",
            result.err()
        );
        assert!(stub_path.exists(), "stub file should be created");

        let contents = std::fs::read_to_string(&stub_path).expect("read stub");
        let parsed = comment_parser::parse_tix_file(&contents);
        assert!(
            parsed.is_ok(),
            "generated stub should parse: {:?}",
            parsed.err()
        );
    }

    #[test]
    fn verify_stubs_passes_for_correct_stub() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let nix_path = dir.path().join("test.nix");
        let stub_path = dir.path().join("test.tix");

        // Simple file that produces an int.
        std::fs::write(&nix_path, "42").expect("write nix file");
        std::fs::write(&stub_path, "val test :: int;\n").expect("write stub file");

        let mismatches = run_verify_stubs(nix_path, stub_path, vec![], false)
            .expect("verify-stubs should succeed");
        assert!(
            mismatches.is_empty(),
            "correct stub should have no mismatches, got: {:?}",
            mismatches.iter().map(|m| &m.val_name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn verify_stubs_detects_mismatch() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let nix_path = dir.path().join("test.nix");
        let stub_path = dir.path().join("test.tix");

        // File produces an int, but stub declares string.
        std::fs::write(&nix_path, "42").expect("write nix file");
        std::fs::write(&stub_path, "val test :: string;\n").expect("write stub file");

        let mismatches = run_verify_stubs(nix_path, stub_path, vec![], false)
            .expect("verify-stubs should succeed (mismatches are in the Ok path)");
        assert!(
            !mismatches.is_empty(),
            "mismatched stub should produce at least one mismatch"
        );
        assert_eq!(mismatches[0].val_name, "test");
    }

    #[test]
    fn verify_stubs_no_val_decls() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let nix_path = dir.path().join("test.nix");
        let stub_path = dir.path().join("test.tix");

        // Stub with only a type alias, no val declarations.
        std::fs::write(&nix_path, "42").expect("write nix file");
        std::fs::write(&stub_path, "type Foo = int;\n").expect("write stub file");

        let mismatches = run_verify_stubs(nix_path, stub_path, vec![], false)
            .expect("verify-stubs should succeed with no val decls");
        assert!(
            mismatches.is_empty(),
            "no val decls means no mismatches to report"
        );
    }
}
