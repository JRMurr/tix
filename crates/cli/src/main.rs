mod check;
mod config;
mod gen_stubs;
mod init;
pub mod json_output;
mod timing;

use std::collections::HashMap;
use std::sync::Arc;
use std::{error::Error, path::PathBuf};

/// Maximum number of diagnostics to render before truncating.
/// Rendering thousands of miette reports against a large source file is
/// expensive (each report re-scans line boundaries). Capping keeps the
/// CLI responsive on huge files like nixpkgs all-packages.nix.
const MAX_RENDERED_DIAGNOSTICS: usize = 200;

use clap::{Parser, Subcommand, ValueEnum};

/// Output format for diagnostics and type information.
#[derive(Clone, Debug, Default, ValueEnum)]
pub enum OutputFormat {
    /// Human-readable colored output (default)
    #[default]
    Human,
    /// Machine-readable JSON
    Json,
}
use lang_ast::{module_and_source_maps, name_resolution, RootDatabase};
use lang_check::aliases::TypeAliasRegistry;
use lang_check::diagnostic::{TixDiagnostic, TixDiagnosticKind};
use lang_check::imports::{import_errors_to_diagnostics, resolve_import_types_from_stubs};
use lang_ty::{OutputTy, TypeArena};
use miette::{LabeledSpan, NamedSource};
use rowan::ast::AstNode;

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

// =============================================================================
// CLI Argument Parsing
// =============================================================================
//
// The CLI supports two modes:
//   1. Type-check mode (default): `tix file.nix [--stubs ...]`
//   2. Subcommand mode: `tix gen-stubs nixos [...]`, `tix lsp`, etc.
//
// Backward compatibility: bare `tix file.nix` works because `file_path`
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

    /// Print per-phase timing and memory usage
    #[arg(long)]
    timing: bool,

    /// Show complete types without truncation
    #[arg(long)]
    full_types: bool,

    /// Output format: human (default) or json
    #[arg(long, value_enum, default_value_t = OutputFormat::Human)]
    format: OutputFormat,
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

        /// Number of parallel inference threads (default: number of CPUs)
        #[arg(short = 'j', long = "jobs", value_name = "N")]
        jobs: Option<usize>,

        /// Print per-phase timing and memory usage
        #[arg(long)]
        timing: bool,

        /// Output format: human (default) or json
        #[arg(long, value_enum)]
        format: Option<OutputFormat>,
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

    /// Start the Language Server (LSP) on stdin/stdout
    Lsp {
        /// RSS memory limit in MiB (default: 80% of system RAM).
        /// Set to 0 to disable. Overrides TIX_MEM_LIMIT env var.
        #[arg(long, value_name = "MIB")]
        mem_limit: Option<u64>,

        /// Log level for tix crates (default: info).
        /// Overridden by the RUST_LOG env var if set.
        #[arg(long, value_name = "LEVEL", default_value = "info")]
        log_level: String,
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
            source_roots: Vec::new(),
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
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args = Cli::parse();

    // The LSP sets up its own logger with custom filters, so skip here.
    if !matches!(args.command, Some(Command::Lsp { .. })) {
        timing::init_tracing(args.timing);
    }

    match args.command {
        Some(Command::Init { path, yes, dry_run }) => init::run_init(path, yes, dry_run),
        Some(Command::Check {
            config_path,
            no_default_stubs,
            verbose,
            jobs,
            timing,
            format,
        }) => check::run_check_project(
            config_path,
            no_default_stubs,
            verbose,
            jobs,
            timing,
            format.unwrap_or(args.format.clone()),
        ),
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
        Some(Command::Lsp {
            mem_limit,
            log_level,
        }) => {
            tix_lsp::run_lsp(mem_limit, Some(log_level));
            Ok(())
        }
        None => {
            let file_path = args
                .file_path
                .ok_or("No file path provided. Usage: tix <file.nix> or tix gen-stubs <source>")?;
            run_check(
                file_path,
                args.stub_paths,
                args.no_default_stubs,
                args.config_path,
                args.timing,
                args.full_types,
                args.format,
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
            source_roots: Vec::new(),
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
    let import_resolution = resolve_import_types_from_stubs(
        &module,
        &name_res,
        base_dir,
        &HashMap::new(),
        Some(&registry),
    );

    let result = lang_check::CheckBuilder::from_db(
        &db,
        file,
        Arc::new(registry),
        import_resolution.types,
        Arc::default(),
    )
    .run();

    let (arena, root_ty) = result
        .inference
        .as_ref()
        .and_then(|inf| {
            inf.expr_ty_map
                .get(module.entry_expr)
                .copied()
                .map(|ty| (inf.arena.clone(), ty))
        })
        .ok_or("Failed to infer root type for file")?;

    // Format as a .tix val declaration.
    // Use the file stem as the declaration name, or "_" as a placeholder.
    let decl_name = file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("_");

    let root_ty_str = format!("{}", arena.display(root_ty));
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

    let import_resolution = resolve_import_types_from_stubs(
        &module,
        &name_res,
        base_dir,
        &HashMap::new(),
        Some(&registry),
    );

    let registry = Arc::new(registry);
    let result = lang_check::CheckBuilder::from_db(
        &db,
        file,
        Arc::clone(&registry),
        import_resolution.types,
        Arc::default(),
    )
    .run();

    let (inf_arena, root_ty) = result
        .inference
        .as_ref()
        .and_then(|inf| {
            inf.expr_ty_map
                .get(module.entry_expr)
                .copied()
                .map(|ty| (inf.arena.clone(), ty))
        })
        .ok_or(VerifyStubsError::NoRootType {
            path: file_path.clone(),
        })?;

    // Compare each declared val against the inferred root type.
    // For a typical single-file stub with one val, this checks the root type.
    let stub_filename = stub_path.display().to_string();
    let mut mismatches = Vec::new();

    for (name, declared_ty, &(span_start, span_end)) in &val_decls {
        let mut decl_arena = TypeArena::new();
        let declared_output = parsed_ty_to_output_ty(declared_ty, &registry, &mut decl_arena, 0);
        let declared_root = decl_arena.intern(declared_output);
        let mut diffs = Vec::new();
        compare_types(
            &inf_arena,
            root_ty,
            &decl_arena,
            declared_root,
            &format!("val {name}"),
            &mut diffs,
        );
        if !diffs.is_empty() {
            mismatches.push(VerifyMismatch {
                val_name: name.to_string(),
                inferred: format!("{}", inf_arena.display(root_ty)),
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
///
/// Each side carries its own arena since inferred and declared types live in
/// separate arenas. All TyRef children are looked up in their respective arena.
fn compare_types(
    inf_arena: &TypeArena,
    inferred: lang_ty::TyRef,
    decl_arena: &TypeArena,
    declared: lang_ty::TyRef,
    path: &str,
    mismatches: &mut Vec<String>,
) {
    let inf_node = &inf_arena[inferred];
    let decl_node = &decl_arena[declared];

    // Type variables in the declared type are wildcards — any inferred type matches.
    if matches!(decl_node, OutputTy::TyVar(_) | OutputTy::Top) {
        return;
    }

    match (inf_node, decl_node) {
        // Attrset comparison: check that all declared fields exist with compatible types.
        (OutputTy::AttrSet(inf_attr), OutputTy::AttrSet(decl_attr)) => {
            // Clone the field maps to avoid holding borrows into the arenas
            // across recursive calls that also borrow the arenas.
            let inf_fields: Vec<_> = inf_attr
                .fields
                .iter()
                .map(|(k, v)| (k.clone(), *v))
                .collect();
            let decl_fields: Vec<_> = decl_attr
                .fields
                .iter()
                .map(|(k, v)| (k.clone(), *v))
                .collect();
            for (field_name, decl_field_ref) in &decl_fields {
                match inf_fields.iter().find(|(k, _)| k == field_name) {
                    Some((_, inf_field_ref)) => {
                        compare_types(
                            inf_arena,
                            *inf_field_ref,
                            decl_arena,
                            *decl_field_ref,
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
            let (inf_p, inf_b, decl_p, decl_b) = (*inf_p, *inf_b, *decl_p, *decl_b);
            compare_types(
                inf_arena,
                inf_p,
                decl_arena,
                decl_p,
                &format!("{path} (param)"),
                mismatches,
            );
            compare_types(
                inf_arena,
                inf_b,
                decl_arena,
                decl_b,
                &format!("{path} (return)"),
                mismatches,
            );
        }

        // List comparison.
        (OutputTy::List(inf_inner), OutputTy::List(decl_inner)) => {
            let (inf_inner, decl_inner) = (*inf_inner, *decl_inner);
            compare_types(
                inf_arena,
                inf_inner,
                decl_arena,
                decl_inner,
                &format!("{path} (list element)"),
                mismatches,
            );
        }

        // Primitive exact match.
        (OutputTy::Primitive(a), OutputTy::Primitive(b)) if a == b => {}

        // Union comparison: each declared member must be compatible with at
        // least one inferred member (or the whole inferred type if it isn't a union).
        (OutputTy::Union(inf_members), OutputTy::Union(decl_members)) => {
            let inf_members: Vec<_> = inf_members.to_vec();
            let decl_members: Vec<_> = decl_members.to_vec();
            for decl_m in &decl_members {
                let mut any_match = false;
                for inf_m in &inf_members {
                    let mut trial = Vec::new();
                    compare_types(inf_arena, *inf_m, decl_arena, *decl_m, path, &mut trial);
                    if trial.is_empty() {
                        any_match = true;
                        break;
                    }
                }
                if !any_match {
                    mismatches.push(format!(
                        "{path}: stub declares union member `{}` but no matching inferred member found",
                        decl_arena.display(*decl_m)
                    ));
                }
            }
        }

        // Intersection comparison: each declared member must be compatible
        // with the inferred type.
        (_, OutputTy::Intersection(decl_members)) => {
            let decl_members: Vec<_> = decl_members.to_vec();
            for decl_m in &decl_members {
                compare_types(inf_arena, inferred, decl_arena, *decl_m, path, mismatches);
            }
        }
        (OutputTy::Intersection(inf_members), _) => {
            // If inferred is an intersection, any member matching suffices.
            let inf_members: Vec<_> = inf_members.to_vec();
            let mut any_match = false;
            for inf_m in &inf_members {
                let mut trial = Vec::new();
                compare_types(inf_arena, *inf_m, decl_arena, declared, path, &mut trial);
                if trial.is_empty() {
                    any_match = true;
                    break;
                }
            }
            if !any_match {
                mismatches.push(format!(
                    "{path}: stub declares `{}` but implementation infers `{}`",
                    decl_arena.display(declared),
                    inf_arena.display(inferred),
                ));
            }
        }

        // Single inferred type vs declared union: inferred must match at least
        // one declared member.
        (_, OutputTy::Union(decl_members)) => {
            let decl_members: Vec<_> = decl_members.to_vec();
            let mut any_match = false;
            for decl_m in &decl_members {
                let mut trial = Vec::new();
                compare_types(inf_arena, inferred, decl_arena, *decl_m, path, &mut trial);
                if trial.is_empty() {
                    any_match = true;
                    break;
                }
            }
            if !any_match {
                mismatches.push(format!(
                    "{path}: stub declares `{}` but implementation infers `{}`",
                    decl_arena.display(declared),
                    inf_arena.display(inferred),
                ));
            }
        }

        // Named types: unwrap and compare inner.
        (OutputTy::Named(_, inf_inner), _) => {
            let inf_inner = *inf_inner;
            compare_types(inf_arena, inf_inner, decl_arena, declared, path, mismatches);
        }
        (_, OutputTy::Named(_, decl_inner)) => {
            let decl_inner = *decl_inner;
            compare_types(
                inf_arena, inferred, decl_arena, decl_inner, path, mismatches,
            );
        }

        // Type kind mismatch.
        _ => {
            mismatches.push(format!(
                "{path}: stub declares `{}` but implementation infers `{}`",
                decl_arena.display(declared),
                inf_arena.display(inferred),
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
    show_timing: bool,
    full_types: bool,
    format: OutputFormat,
) -> Result<(), Box<dyn Error>> {
    let mut timer = timing::Timer::new(show_timing);

    let mut registry = build_registry(no_default_stubs, &stub_paths)?;
    timer.mark("registry");

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
        // Runtime stub generation: if TIX_BUILTIN_STUBS is not set and
        // [stubs.generate] is configured, generate stubs via nix build.
        maybe_generate_stubs(&mut registry, &cfg.stubs, dir);

        for stub in cfg.stubs.paths() {
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
                Arc::default()
            },
        )
    } else {
        Arc::default()
    };

    let db: RootDatabase = Default::default();

    let file = db.read_file(file_path.clone())?;

    let (module, source_map) = module_and_source_maps(&db, file);
    let name_res = name_resolution(&db, file);
    let module_indices = lang_ast::module_indices(&db, file);
    let grouped_defs = lang_ast::group_def(&db, file);
    timer.mark("parse+lower+nameres");

    let base_dir = file_path.parent().unwrap_or(std::path::Path::new("/"));

    // Demand-driven import resolution: use the coordinator to recursively
    // infer imported files so cross-file types are available.
    let registry = Arc::new(registry);
    let coordinator = lang_check::coordinator::InferenceCoordinator::new();

    // Build a syntax provider that wraps the DB for transitive imports.
    // Unlike the root file (whose context_args are resolved above), transitive
    // imports need per-file context resolution from tix.toml so each file gets
    // the correct parameter typing (e.g. NixOS modules vs home-manager files).
    struct SingleFileSyntaxProvider {
        db: parking_lot::Mutex<RootDatabase>,
        registry: parking_lot::Mutex<Arc<lang_check::aliases::TypeAliasRegistry>>,
        /// tix.toml config + directory, used to resolve per-file context_args.
        config: Option<(config::TixConfig, std::path::PathBuf)>,
    }
    impl lang_check::coordinator::SyntaxProvider for SingleFileSyntaxProvider {
        fn syntax_for_file(&self, path: &std::path::Path) -> Option<lang_check::SyntaxBundle> {
            let db = self.db.lock();
            let nix_file = db.read_file(path.to_path_buf()).ok()?;
            let (module, _) = module_and_source_maps(&*db, nix_file);
            let module_indices = lang_ast::module_indices(&*db, nix_file);
            let name_res = name_resolution(&*db, nix_file);
            let grouped_defs = lang_ast::group_def(&*db, nix_file);

            // Resolve context_args from tix.toml for this specific file,
            // so transitive imports get their own context (not the root's).
            let (context_args, registry) = {
                let mut reg = self.registry.lock();
                let context_args = if let Some((ref cfg, ref dir)) = self.config {
                    config::resolve_context_for_file(path, cfg, dir, Arc::make_mut(&mut reg))
                        .unwrap_or_default()
                } else {
                    Arc::default()
                };
                (context_args, Arc::clone(&reg))
            };

            Some(lang_check::SyntaxBundle {
                path: path.to_path_buf(),
                module,
                module_indices,
                name_res,
                grouped_defs,
                registry,
                context_args,
            })
        }
    }

    let syntax_provider = SingleFileSyntaxProvider {
        db: parking_lot::Mutex::new(db),
        registry: parking_lot::Mutex::new(Arc::clone(&registry)),
        config: toml_config
            .as_ref()
            .zip(config_dir.as_ref())
            .map(|(cfg, dir)| (cfg.clone(), dir.clone())),
    };

    // Resolve imports using the coordinator (demand-driven).
    let import_resolution = lang_check::imports::resolve_import_types(
        &module,
        &name_res,
        base_dir,
        |dep_path| {
            // Demand the dependency's type from the coordinator.
            let result = coordinator.demand_file(dep_path, &syntax_provider)?;
            result.signature.map(|s| s.root_ty)
        },
        Some(&registry),
    );

    let import_diagnostics = import_errors_to_diagnostics(&import_resolution.errors);
    timer.mark("import-resolution");

    let mut result = lang_check::CheckBuilder::from_precomputed(
        module.clone(),
        name_res,
        module_indices,
        grouped_defs,
        registry,
        import_resolution.types,
        context_args,
    )
    .run();
    timer.mark("inference+collect");

    // Merge import diagnostics into the check result.
    result.diagnostics.extend(import_diagnostics);

    // If inference timed out, identify which bindings are incomplete
    // and include them in the diagnostic for actionable feedback.
    if result.bailed_out {
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
            kind: TixDiagnosticKind::InferenceAborted { missing_bindings },
        });
    }

    let source_text = std::fs::read_to_string(&file_path)?;

    // Apply suppression directives: `# tix-nocheck` clears all diagnostics,
    // `# tix-ignore` filters diagnostics on the next line.
    if module.nocheck {
        result.diagnostics.clear();
    } else if !module.ignore_lines.is_empty() {
        let root = rnix::Root::parse(&source_text).tree();
        result.diagnostics = lang_check::diagnostic::filter_ignored_diagnostics(
            result.diagnostics,
            &module.ignore_lines,
            &source_map,
            root.syntax(),
            &source_text,
        );
    }

    // Collect binding types and root type (shared by both output modes).
    let display_config = if full_types {
        lang_ty::DisplayConfig::full()
    } else {
        lang_ty::DisplayConfig::cli()
    };

    let (bindings_map, root_type_str) =
        collect_bindings_and_root(&result, &module, &display_config);

    match format {
        OutputFormat::Human => {
            let (error_count, _warning_count) =
                render_diagnostics(&file_path, &source_text, &result.diagnostics, &source_map);

            if error_count > 0 {
                std::process::exit(1);
            }

            timer.mark("diagnostics");

            if result.inference.is_some() {
                println!("Bindings:");
                for (name, ty_str) in &bindings_map {
                    println!("  {name} :: {ty_str}");
                }
                match &root_type_str {
                    Some(root) => println!("\nRoot type:\n  {root}"),
                    None => {
                        eprintln!("error: could not infer type for root expression");
                        std::process::exit(1);
                    }
                }
            }
        }
        OutputFormat::Json => {
            let (file_result, error_count, warning_count) = json_output::diagnostics_to_json(
                &file_path,
                &source_text,
                &result.diagnostics,
                &source_map,
            );

            timer.mark("diagnostics");

            let output = json_output::JsonOutput {
                version: 1,
                files: vec![file_result],
                summary: json_output::JsonSummary {
                    files_checked: 1,
                    errors: error_count,
                    warnings: warning_count,
                },
                bindings: if bindings_map.is_empty() {
                    None
                } else {
                    Some(bindings_map)
                },
                root_type: root_type_str,
            };

            json_output::write_json_output(&output)?;

            if error_count > 0 {
                std::process::exit(1);
            }
        }
    }

    timer.summary();

    Ok(())
}

/// Collect deduplicated binding types and root type from inference results.
/// Returns `(bindings_map, root_type_string)`. Both are empty/None if inference
/// didn't produce results.
fn collect_bindings_and_root(
    result: &lang_check::CheckResult,
    module: &lang_ast::Module,
    display_config: &lang_ty::DisplayConfig,
) -> (std::collections::BTreeMap<String, String>, Option<String>) {
    let mut bindings = std::collections::BTreeMap::new();
    let mut root_type = None;

    if let Some(inference) = &result.inference {
        // Deduplicate by name text. Prefer definitions (PatField, Param, LetIn)
        // over PlainAttrset keys, then prefer types without unions/intersections.
        let mut seen =
            std::collections::BTreeMap::<String, (lang_ast::NameKind, lang_ty::TyRef)>::new();
        for (name_id, name) in module.names() {
            if let Some(ty) = inference.name_ty_map.get(name_id).copied() {
                seen.entry(name.text.to_string())
                    .and_modify(|(existing_kind, existing_ty)| {
                        if !existing_kind.is_definition() && name.kind.is_definition() {
                            *existing_kind = name.kind;
                            *existing_ty = ty;
                        } else if existing_kind.is_definition() && !name.kind.is_definition() {
                            // Keep existing definition type.
                        } else if inference.arena.contains_union_or_intersection(ty)
                            && !inference.arena.contains_union_or_intersection(*existing_ty)
                        {
                            // Keep existing (cleaner) one.
                        } else if !inference.arena.contains_union_or_intersection(ty)
                            && inference.arena.contains_union_or_intersection(*existing_ty)
                        {
                            *existing_kind = name.kind;
                            *existing_ty = ty;
                        }
                    })
                    .or_insert((name.kind, ty));
            }
        }

        for (name, (_kind, ty)) in &seen {
            bindings.insert(
                name.clone(),
                inference
                    .arena
                    .display_truncated(*ty, display_config)
                    .to_string(),
            );
        }

        root_type = inference
            .expr_ty_map
            .get(module.entry_expr)
            .copied()
            .map(|ty| {
                inference
                    .arena
                    .display_truncated(ty, display_config)
                    .to_string()
            });
    }

    (bindings, root_type)
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

    // Share the source text across all diagnostics instead of cloning per
    // report. Each NamedSource previously copied the entire file, which for
    // a 12k-line file × 2000 diagnostics meant ~400MB of allocations and
    // redundant line-boundary scans in miette.
    let shared_source: Arc<NamedSource<String>> =
        Arc::new(NamedSource::new(filename, source_text.to_string()));

    let mut rendered = 0;
    for diag in diagnostics {
        let is_warning = diag.kind.is_warning();
        if is_warning {
            warning_count += 1;
        } else {
            error_count += 1;
        }

        // After MAX_RENDERED_DIAGNOSTICS, still count but skip rendering.
        if rendered >= MAX_RENDERED_DIAGNOSTICS {
            continue;
        }
        rendered += 1;

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

        // Format: "error[E001]: message" or "warning[E012]: message"
        let level = if is_warning { "warning" } else { "error" };
        let message = format!("{level}[{}]: {}", diag.kind.code(), diag.kind);

        let mut builder = miette::MietteDiagnostic::new(message).with_url(diag.kind.docs_url());
        if !labels.is_empty() {
            builder = builder.with_labels(labels);
        }
        if let Some(help_text) = help {
            builder = builder.with_help(help_text);
        }
        if is_warning {
            builder = builder.with_severity(miette::Severity::Warning);
        }

        let report = miette::Report::new(builder).with_source_code(shared_source.clone());
        eprintln!("{:?}", report);
    }

    let suppressed = diagnostics.len().saturating_sub(MAX_RENDERED_DIAGNOSTICS);
    if suppressed > 0 {
        eprintln!(
            "... and {suppressed} more diagnostic{} (showing first {MAX_RENDERED_DIAGNOSTICS})",
            if suppressed == 1 { "" } else { "s" }
        );
    }

    (error_count, warning_count)
}

/// If `TIX_BUILTIN_STUBS` is not set and `[stubs.generate]` is configured,
/// attempt runtime stub generation and set the registry's builtin stubs dir.
fn maybe_generate_stubs(
    registry: &mut TypeAliasRegistry,
    stubs_config: &tix_lsp::project_config::StubsConfig,
    config_dir: &std::path::Path,
) {
    // TIX_BUILTIN_STUBS takes priority — skip runtime generation.
    if std::env::var("TIX_BUILTIN_STUBS").is_ok() {
        return;
    }

    if let Some(gen_config) = stubs_config.generate() {
        match tix_lsp::store_stubs::generate_stubs(gen_config, config_dir) {
            Ok(result) => {
                eprintln!("Using generated stubs: {}", result.stubs_dir.display());
                registry.set_builtin_stubs_dir(result.stubs_dir);
                for (id, root) in &result.source_roots {
                    registry.set_source_root(id.as_str(), root.clone());
                }
            }
            Err(e) => {
                eprintln!("Warning: stub generation failed, using defaults: {e}");
            }
        }
    }
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
                if let Some(name) = entry_path.file_name().and_then(|n| n.to_str()) {
                    if comment_parser::SKIP_STUB_DIRS.contains(&name) {
                        continue;
                    }
                }
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
    registry.load_tix_file_with_path(&file, path);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang_ty::{AttrSetTy, PrimitiveTy, TypeArena};

    // Build a single-node arena containing the given OutputTy and return
    // (arena, root_ref). Used by compare_types tests which need an arena context.
    fn make_arena(ty: OutputTy) -> (TypeArena, lang_ty::TyRef) {
        let mut arena = TypeArena::new();
        let root = arena.intern(ty);
        (arena, root)
    }

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
        let (ia, ir) = make_arena(oty_int());
        let (da, dr) = make_arena(oty_int());
        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(m.is_empty(), "same primitives should match");
    }

    #[test]
    fn compare_types_different_primitive_mismatch() {
        let (ia, ir) = make_arena(oty_int());
        let (da, dr) = make_arena(oty_string());
        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert_eq!(m.len(), 1, "different primitives should mismatch");
        assert!(m[0].contains("root"));
    }

    #[test]
    fn compare_types_tyvar_declared_is_wildcard() {
        let (ia, ir) = make_arena(oty_int());
        let (da, dr) = make_arena(OutputTy::TyVar(0));
        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(m.is_empty(), "TyVar in declared should match anything");
    }

    #[test]
    fn compare_types_top_declared_is_wildcard() {
        let (ia, ir) = make_arena(oty_int());
        let (da, dr) = make_arena(OutputTy::Top);
        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(m.is_empty(), "Top in declared should match anything");
    }

    #[test]
    fn compare_types_attrset_missing_field() {
        let (ia, ir) = make_arena(OutputTy::AttrSet(AttrSetTy {
            fields: std::collections::BTreeMap::new(),
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        }));
        let mut decl_arena = TypeArena::new();
        let x_int = decl_arena.intern(oty_int());
        let mut decl_fields = std::collections::BTreeMap::new();
        decl_fields.insert(smol_str::SmolStr::from("x"), x_int);
        let dr = decl_arena.intern(OutputTy::AttrSet(AttrSetTy {
            fields: decl_fields,
            dyn_ty: None,
            open: false,
            optional_fields: std::collections::BTreeSet::new(),
        }));
        let mut m = Vec::new();
        compare_types(&ia, ir, &decl_arena, dr, "root", &mut m);
        assert_eq!(m.len(), 1, "missing field should produce mismatch");
        assert!(m[0].contains("x"));
    }

    #[test]
    fn compare_types_union_match() {
        let mut ia = TypeArena::new();
        let ii = ia.intern(oty_int());
        let is = ia.intern(oty_string());
        let ir = ia.intern(OutputTy::Union(vec![ii, is]));

        let mut da = TypeArena::new();
        let di = da.intern(oty_int());
        let ds = da.intern(oty_string());
        let dr = da.intern(OutputTy::Union(vec![di, ds]));

        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(m.is_empty(), "matching unions should be compatible");
    }

    #[test]
    fn compare_types_union_mismatch() {
        let mut ia = TypeArena::new();
        let ii = ia.intern(oty_int());
        let ir = ia.intern(OutputTy::Union(vec![ii]));

        let mut da = TypeArena::new();
        let ds = da.intern(oty_string());
        let dr = da.intern(OutputTy::Union(vec![ds]));

        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(!m.is_empty(), "non-matching unions should mismatch");
    }

    #[test]
    fn compare_types_intersection_declared() {
        let (ia, ir) = make_arena(oty_int());

        let mut da = TypeArena::new();
        let di = da.intern(oty_int());
        let dr = da.intern(OutputTy::Intersection(vec![di]));

        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
        assert!(
            m.is_empty(),
            "inferred matching all intersection members should pass"
        );
    }

    #[test]
    fn compare_types_lambda_match() {
        let mut ia = TypeArena::new();
        let ip = ia.intern(oty_int());
        let ib = ia.intern(oty_string());
        let ir = ia.intern(OutputTy::Lambda {
            param: ip,
            body: ib,
        });

        let mut da = TypeArena::new();
        let dp = da.intern(oty_int());
        let db = da.intern(oty_string());
        let dr = da.intern(OutputTy::Lambda {
            param: dp,
            body: db,
        });

        let mut m = Vec::new();
        compare_types(&ia, ir, &da, dr, "root", &mut m);
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
