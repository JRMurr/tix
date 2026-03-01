// =============================================================================
// gen-stubs: Auto-generate .tix declaration files from external sources
// =============================================================================
//
// Currently supports NixOS option tree extraction. The architecture is designed
// to accommodate future sources (pkgs, lib, home-manager) via additional
// subcommands.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

use serde::Deserialize;

// =============================================================================
// NixOS Option JSON Schema
// =============================================================================
//
// These types mirror the JSON structure produced by tools/extract-options.nix.
// The option tree is a recursive structure where each node is either a leaf
// option (with type info) or a namespace containing children.

#[derive(Debug, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum OptionNode {
    Option(OptionLeaf),
    Namespace(NamespaceNode),
}

#[derive(Debug, Deserialize, PartialEq)]
pub struct OptionLeaf {
    #[serde(rename = "_isOption")]
    pub _is_option: bool, // always true
    #[serde(rename = "typeInfo")]
    pub type_info: NixosTypeInfo,
    /// NixOS option description text, extracted from the option declaration.
    #[serde(default)]
    pub description: Option<String>,
}

#[derive(Debug, Deserialize, PartialEq)]
pub struct NamespaceNode {
    #[serde(rename = "_isOption")]
    pub _is_option: bool, // always false
    pub children: std::collections::BTreeMap<String, OptionNode>,
}

/// Type representation extracted from NixOS option declarations.
/// Each variant maps to a NixOS `types.*` constructor.
#[derive(Debug, Deserialize, PartialEq)]
#[serde(tag = "type")]
pub enum NixosTypeInfo {
    #[serde(rename = "primitive")]
    Primitive { value: String },
    #[serde(rename = "package")]
    Package,
    #[serde(rename = "list")]
    List { elem: Box<NixosTypeInfo> },
    #[serde(rename = "attrsOf")]
    AttrsOf { elem: Box<NixosTypeInfo> },
    #[serde(rename = "nullOr")]
    NullOr { elem: Box<NixosTypeInfo> },
    #[serde(rename = "union")]
    Union { members: Vec<NixosTypeInfo> },
    #[serde(rename = "enum")]
    Enum,
    #[serde(rename = "submodule")]
    Submodule {
        options: std::collections::BTreeMap<String, OptionNode>,
    },
    #[serde(rename = "function")]
    Function { result: Box<NixosTypeInfo> },
    #[serde(rename = "anything")]
    Anything,
}

// =============================================================================
// Type → .tix Syntax Conversion
// =============================================================================
//
// Converts extracted NixOS types into .tix type expression strings. Handles
// operator precedence: arrows bind loosest, then unions, then intersections,
// then atoms. Parentheses are inserted only when necessary.

/// Precedence levels for .tix type expressions.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum Prec {
    Arrow,      // lowest: `a -> b`
    Union,      // `a | b`
    _Intersect, // `a & b` (unused for now — no NixOS types produce intersections)
    _Atom,      // highest: primitives, parens, lists, attrsets
}

/// Convert a NixOS type to a .tix type expression string.
pub fn type_to_tix(ty: &NixosTypeInfo) -> String {
    type_to_tix_prec(ty, Prec::Arrow)
}

fn type_to_tix_prec(ty: &NixosTypeInfo, ctx: Prec) -> String {
    match ty {
        NixosTypeInfo::Primitive { value } => value.clone(),

        // Packages are derivations — the Derivation type alias is always
        // available from the built-in lib.tix stubs.
        NixosTypeInfo::Package => "Derivation".to_string(),

        NixosTypeInfo::List { elem } => {
            format!("[{}]", type_to_tix_prec(elem, Prec::Arrow))
        }

        NixosTypeInfo::AttrsOf { elem } => {
            format!("{{ _: {} }}", type_to_tix_prec(elem, Prec::Arrow))
        }

        NixosTypeInfo::NullOr { elem } => {
            let inner = type_to_tix_prec(elem, Prec::Union);
            let result = format!("{} | null", inner);
            if ctx > Prec::Union {
                format!("({})", result)
            } else {
                result
            }
        }

        NixosTypeInfo::Union { members } => {
            if members.is_empty() {
                "{ ... }".to_string()
            } else {
                let parts: Vec<String> = members
                    .iter()
                    .map(|m| type_to_tix_prec(m, Prec::Union))
                    .collect();
                let result = parts.join(" | ");
                if ctx > Prec::Union {
                    format!("({})", result)
                } else {
                    result
                }
            }
        }

        // TODO: use literal types when supported (e.g. `"enabled" | "disabled"`)
        NixosTypeInfo::Enum => "string".to_string(),

        NixosTypeInfo::Submodule { options } => options_to_attrset_ty(options, 0),

        NixosTypeInfo::Function { result } => {
            let res = type_to_tix_prec(result, Prec::Arrow);
            let result_str = format!("{{ ... }} -> {}", res);
            if ctx > Prec::Arrow {
                format!("({})", result_str)
            } else {
                result_str
            }
        }

        NixosTypeInfo::Anything => "{ ... }".to_string(),
    }
}

// =============================================================================
// Option Tree → Attrset Type
// =============================================================================
//
// Walks the option tree and produces a .tix attrset type string with proper
// indentation. Namespaces become nested open attrsets, options become typed
// fields.

/// Check whether a field name is a valid bare identifier in .tix syntax.
/// If not, it needs to be quoted.
fn needs_quoting(name: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    // Must match the `identifier` rule in tix_decl.pest:
    //   ASCII_ALPHA ~ (ASCII_ALPHANUMERIC | "_" | "'" | "-")*
    // | "_" ~ (ASCII_ALPHANUMERIC | "_" | "'" | "-")+
    // | ASCII_DIGIT ~ (ASCII_ALPHANUMERIC | "_" | "'" | "-")*
    // Also must not be bare `_` (reserved for dyn_field).
    if name == "_" {
        return true;
    }
    let first = name.as_bytes()[0];
    let valid_first = first.is_ascii_alphabetic() || first == b'_' || first.is_ascii_digit();
    if !valid_first {
        return true;
    }
    // Underscore-led names need at least one continuation character.
    if first == b'_' && name.len() == 1 {
        return true;
    }
    name.bytes()
        .skip(1)
        .any(|b| !b.is_ascii_alphanumeric() && b != b'_' && b != b'\'' && b != b'-')
}

/// Format a field name, quoting it if it contains characters not valid
/// as bare identifiers (e.g. dots in `net.core.rmem_max`).
fn format_field_name(name: &str) -> String {
    if needs_quoting(name) {
        format!("\"{}\"", name)
    } else {
        name.to_string()
    }
}

/// Convert an option tree (BTreeMap from the JSON) to a .tix attrset type string.
/// When `emit_docs` is true, option descriptions are emitted as `##` doc comments.
pub fn options_to_attrset_ty(
    options: &std::collections::BTreeMap<String, OptionNode>,
    indent: usize,
) -> String {
    options_to_attrset_ty_inner(options, indent, false)
}

/// Like `options_to_attrset_ty` but with doc comment emission control.
pub fn options_to_attrset_ty_with_docs(
    options: &std::collections::BTreeMap<String, OptionNode>,
    indent: usize,
    full_descriptions: bool,
) -> String {
    options_to_attrset_ty_inner(options, indent, full_descriptions)
}

fn options_to_attrset_ty_inner(
    options: &std::collections::BTreeMap<String, OptionNode>,
    indent: usize,
    emit_docs: bool,
) -> String {
    if options.is_empty() {
        return "{ ... }".to_string();
    }

    let pad = "  ".repeat(indent + 1);
    let close_pad = "  ".repeat(indent);
    let mut fields = Vec::new();

    for (name, node) in options {
        let field_name = format_field_name(name);
        match node {
            OptionNode::Option(leaf) => {
                let ty_str = type_to_tix(&leaf.type_info);
                let mut lines = String::new();

                // Emit doc comment if we have a description.
                if emit_docs {
                    if let Some(ref desc) = leaf.description {
                        let doc_text = format_description(desc);
                        for doc_line in doc_text.lines() {
                            if doc_line.is_empty() {
                                lines.push_str(&format!("{}##\n", pad));
                            } else {
                                lines.push_str(&format!("{}## {}\n", pad, doc_line));
                            }
                        }
                    }
                }

                lines.push_str(&format!("{}{}: {}", pad, field_name, ty_str));
                fields.push(lines);
            }
            OptionNode::Namespace(ns) => {
                let nested = options_to_attrset_ty_inner(&ns.children, indent + 1, emit_docs);
                fields.push(format!("{}{}: {}", pad, field_name, nested));
            }
        }
    }

    // Open attrset (with `...`) since NixOS modules can extend config freely.
    format!("{{\n{},\n{}...\n{}}}", fields.join(",\n"), pad, close_pad,)
}

/// Format a description for emission as `##` doc comment lines.
/// By default, uses only the first paragraph (up to the first blank line).
fn format_description(desc: &str) -> String {
    // Take the first paragraph only — NixOS descriptions often have lengthy
    // multi-paragraph explanations that are too verbose for inline docs.
    let trimmed = desc.trim();
    match trimmed.find("\n\n") {
        Some(idx) => trimmed[..idx].to_string(),
        None => trimmed.to_string(),
    }
}

// =============================================================================
// .tix File Generation
// =============================================================================

/// The kind of stub file being generated, controlling the type alias name
/// and the context val declarations included in the output.
pub enum StubKind {
    Nixos,
    HomeManager,
}

impl StubKind {
    fn type_name(&self) -> &'static str {
        match self {
            StubKind::Nixos => "NixosConfig",
            StubKind::HomeManager => "HomeManagerConfig",
        }
    }

    fn label(&self) -> &'static str {
        match self {
            StubKind::Nixos => "NixOS",
            StubKind::HomeManager => "Home Manager",
        }
    }

    fn command(&self) -> &'static str {
        match self {
            StubKind::Nixos => "tix-cli gen-stubs nixos",
            StubKind::HomeManager => "tix-cli gen-stubs home-manager",
        }
    }

    fn context_key(&self) -> &'static str {
        match self {
            StubKind::Nixos => "nixos",
            StubKind::HomeManager => "home",
        }
    }

    fn example_glob(&self) -> &'static str {
        match self {
            StubKind::Nixos => "modules/**/*.nix",
            StubKind::HomeManager => "home/**/*.nix",
        }
    }

    fn context_vals(&self) -> &'static str {
        match self {
            // NixOS module arguments: { config, lib, pkgs, options, modulesPath, ... }
            // `options` is the option *declaration* tree, not the evaluated config.
            // Each leaf is an option descriptor, not the final value — use `{ ... }`
            // rather than NixosConfig to avoid false type errors on `options.*.default`.
            StubKind::Nixos => {
                "val config :: NixosConfig;\n\
                 val lib :: Lib;\n\
                 val pkgs :: Pkgs;\n\
                 val options :: { ... };\n\
                 val modulesPath :: path;\n"
            }
            // Home Manager module arguments: { config, lib, pkgs, options, osConfig, ... }
            StubKind::HomeManager => {
                "val config :: HomeManagerConfig;\n\
                 val lib :: Lib;\n\
                 val pkgs :: Pkgs;\n\
                 val options :: { ... };\n\
                 val osConfig :: { ... };\n"
            }
        }
    }
}

/// Generate a complete .tix file string from an option tree.
///
/// The output includes:
///   - A type alias (`NixosConfig` or `HomeManagerConfig`)
///   - Context val declarations (`config`, `lib`, `pkgs`, etc.) so the file
///     can serve as a drop-in replacement for the `@nixos` or `@home-manager`
///     built-in context stubs with real typed config.
///
/// When `full_descriptions` is true, option descriptions are emitted as `##`
/// doc comment lines above each field.
#[cfg(test)]
pub fn generate_tix_file(
    options: &std::collections::BTreeMap<String, OptionNode>,
    kind: &StubKind,
) -> String {
    generate_tix_file_with_docs(options, kind, false)
}

/// Like `generate_tix_file` but with explicit doc comment control.
pub fn generate_tix_file_with_docs(
    options: &std::collections::BTreeMap<String, OptionNode>,
    kind: &StubKind,
    full_descriptions: bool,
) -> String {
    let attrset_ty = options_to_attrset_ty_with_docs(options, 0, full_descriptions);
    let type_name = kind.type_name();
    let command = kind.command();
    let label = kind.label();
    let ctx = kind.context_key();
    let example_glob = kind.example_glob();
    let context_vals = kind.context_vals();

    format!(
        "# Auto-generated {label} option type stubs.\n\
         # Generated by: {command}\n\
         #\n\
         # Re-generate with: {command} -o <this-file>\n\
         #\n\
         # Use in tix.toml as a context stub to get typed config:\n\
         #\n\
         #   [context.{ctx}]\n\
         #   paths = [\"{example_glob}\"]\n\
         #   stubs = [\"./path/to/this-file.tix\"]\n\
         \n\
         type {type_name} = {attrset_ty};\n\
         \n\
         {context_vals}",
    )
}

// =============================================================================
// Nix Evaluation
// =============================================================================
//
// Shells out to `nix eval --json` with our extraction expression embedded.
// Supports two modes:
//   1. Nixpkgs mode: evaluate `(import <nixpkgs/nixos> {}).options`
//   2. Flake mode: evaluate a specific nixosConfiguration from a flake

/// Shared options for all `gen-stubs` subcommands.
pub struct CommonOptions {
    pub nixpkgs: Option<PathBuf>,
    pub flake: Option<PathBuf>,
    /// Pre-computed option tree JSON. When set, skip `nix eval` and read from this file.
    pub from_json: Option<PathBuf>,
    pub output: Option<PathBuf>,
    pub max_depth: u32,
    /// Emit `##` doc comments with option descriptions.
    pub descriptions: bool,
}

/// Options for the `gen-stubs nixos` subcommand.
pub struct NixosOptions {
    pub common: CommonOptions,
    pub hostname: Option<String>,
}

/// Options for the `gen-stubs home-manager` subcommand.
pub struct HomeManagerOptions {
    pub common: CommonOptions,
    /// Explicit path to a home-manager source tree (default: flake registry).
    pub home_manager: Option<PathBuf>,
    /// Username to select from `homeConfigurations` (required if flake has multiple).
    pub username: Option<String>,
}

/// Build the full nix expression that imports extract-options.nix and passes
/// the correct `options` argument.
fn build_nix_expr(opts: &NixosOptions) -> String {
    let extractor = include_str!("../../../tools/extract-options.nix");

    // Build the expression that produces the NixOS option tree.
    // `eval-config.nix` is used instead of `<nixpkgs/nixos>` because the latter
    // requires a `nixos-config` in NIX_PATH. eval-config.nix with an empty module
    // list gives us the full NixOS option tree without needing a system configuration.
    let options_expr = if let Some(ref flake_path) = opts.common.flake {
        let flake = flake_path.display();
        if let Some(ref host) = opts.hostname {
            format!("(builtins.getFlake \"{flake}\").nixosConfigurations.\"{host}\".options")
        } else {
            // Try the sole configuration, or fall back to "default".
            format!(
                "let flake = builtins.getFlake \"{flake}\"; \
                 hosts = builtins.attrNames flake.nixosConfigurations; \
                 name = if builtins.length hosts == 1 then builtins.head hosts \
                        else \"default\"; \
                 in flake.nixosConfigurations.${{name}}.options"
            )
        }
    } else {
        let nixpkgs = match opts.common.nixpkgs {
            Some(ref p) => format!("{}", p.display()),
            None => "<nixpkgs>".to_string(),
        };
        format!(
            "(import ({nixpkgs} + \"/nixos/lib/eval-config.nix\") {{ modules = [ {{ _module.check = false; }} ]; }}).options"
        )
    };

    format!(
        "let extract = {}; in extract {{ options = {}; maxDepth = {}; }}",
        extractor, options_expr, opts.common.max_depth,
    )
}

// =============================================================================
// Home Manager Nix Evaluation
// =============================================================================
//
// Home Manager evaluation is more complex than NixOS because:
//   1. HM extends `lib` with `lib.hm.*` helpers that modules depend on
//   2. HM modules need `pkgs` and `osConfig` as module arguments
//   3. The module list is loaded via `modules/modules.nix`, not eval-config.nix
//
// Supports three modes:
//   1. Registry mode (default): fetch HM from the flake registry
//   2. Explicit path: use a local home-manager source tree
//   3. Flake mode: extract options from a flake's homeConfigurations

/// Build the nix expression for evaluating Home Manager options.
fn build_hm_nix_expr(opts: &HomeManagerOptions) -> String {
    let extractor = include_str!("../../../tools/extract-options.nix");

    // Determine how to get the home-manager source.
    let hm_source = if let Some(ref flake_path) = opts.common.flake {
        let flake = flake_path.display();
        // In flake mode, get the options directly from a homeConfiguration.
        let options_expr = if let Some(ref user) = opts.username {
            format!("(builtins.getFlake \"{flake}\").homeConfigurations.\"{user}\".options")
        } else {
            format!(
                "let flake = builtins.getFlake \"{flake}\"; \
                 users = builtins.attrNames flake.homeConfigurations; \
                 name = if builtins.length users == 1 then builtins.head users \
                        else \"default\"; \
                 in flake.homeConfigurations.${{name}}.options"
            )
        };

        // Flake mode: options come directly from the evaluated configuration.
        return format!(
            "let extract = {}; in extract {{ options = {}; maxDepth = {}; }}",
            extractor, options_expr, opts.common.max_depth,
        );
    } else {
        // Non-flake mode: load HM from explicit path or registry.
        match opts.home_manager {
            Some(ref p) => format!("{}", p.display()),
            None => r#"builtins.getFlake "home-manager""#.to_string(),
        }
    };

    let nixpkgs = match opts.common.nixpkgs {
        Some(ref p) => format!("import {} {{}}", p.display()),
        None => "import <nixpkgs> {}".to_string(),
    };

    // Home Manager extends lib with `lib.hm.*` helpers that many modules
    // reference. We import HM's lib overlay and apply it before loading
    // the module list.
    format!(
        r#"let
  extract = {extractor};
  pkgs = {nixpkgs};
  hmSrc = {hm_source};
  hmLib = import (hmSrc + "/modules/lib") {{ lib = pkgs.lib; }};
  extendedLib = pkgs.lib.extend (self: super: {{ hm = hmLib; }});
  hmModuleList = import (hmSrc + "/modules/modules.nix") {{
    inherit pkgs;
    lib = extendedLib;
    check = false;
  }};
  eval = extendedLib.evalModules {{
    modules = hmModuleList ++ [{{
      _module.check = false;
      _module.args = {{
        inherit pkgs;
        osConfig = {{}};
      }};
    }}];
  }};
in extract {{ options = eval.options; maxDepth = {max_depth}; }}"#,
        max_depth = opts.common.max_depth,
    )
}

/// Run `nix eval --json --impure --expr <expr>`, parse the JSON output into
/// an option tree. `label` is used in the progress message (e.g. "NixOS").
fn invoke_nix_eval_common(
    expr: &str,
    label: &str,
) -> Result<std::collections::BTreeMap<String, OptionNode>, Box<dyn std::error::Error>> {
    let mut cmd = Command::new("nix");
    cmd.args(["eval", "--json", "--expr", expr]);
    cmd.arg("--impure");

    eprintln!("Evaluating {label} options (this may take a while)...");
    let output = cmd.output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("nix eval failed:\n{}", stderr).into());
    }

    let tree: std::collections::BTreeMap<String, OptionNode> =
        serde_json::from_slice(&output.stdout)?;
    Ok(tree)
}

/// Invoke `nix eval --json` for Home Manager and parse the result.
pub fn invoke_hm_nix_eval(
    opts: &HomeManagerOptions,
) -> Result<std::collections::BTreeMap<String, OptionNode>, Box<dyn std::error::Error>> {
    invoke_nix_eval_common(&build_hm_nix_expr(opts), "Home Manager")
}

/// Invoke `nix eval --json` for NixOS and parse the result.
pub fn invoke_nix_eval(
    opts: &NixosOptions,
) -> Result<std::collections::BTreeMap<String, OptionNode>, Box<dyn std::error::Error>> {
    invoke_nix_eval_common(&build_nix_expr(opts), "NixOS")
}

// =============================================================================
// Entry Point
// =============================================================================

/// Read a pre-computed option tree JSON file.
fn read_json_file(
    path: &std::path::Path,
) -> Result<std::collections::BTreeMap<String, OptionNode>, Box<dyn std::error::Error>> {
    let data =
        std::fs::read(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
    let tree = serde_json::from_slice(&data)
        .map_err(|e| format!("failed to parse JSON from {}: {}", path.display(), e))?;
    Ok(tree)
}

/// Run the `gen-stubs nixos` subcommand.
pub fn run_nixos(opts: NixosOptions) -> Result<(), Box<dyn std::error::Error>> {
    let tree = match opts.common.from_json {
        Some(ref path) => read_json_file(path)?,
        None => invoke_nix_eval(&opts)?,
    };
    let tix_content =
        generate_tix_file_with_docs(&tree, &StubKind::Nixos, opts.common.descriptions);
    write_generated_stubs(&tix_content, opts.common.output.as_ref(), "NixOS")
}

/// Run the `gen-stubs home-manager` subcommand.
pub fn run_home_manager(opts: HomeManagerOptions) -> Result<(), Box<dyn std::error::Error>> {
    let tree = match opts.common.from_json {
        Some(ref path) => read_json_file(path)?,
        None => invoke_hm_nix_eval(&opts)?,
    };
    let tix_content =
        generate_tix_file_with_docs(&tree, &StubKind::HomeManager, opts.common.descriptions);
    write_generated_stubs(&tix_content, opts.common.output.as_ref(), "Home Manager")
}

// =============================================================================
// Pkgs Classification
// =============================================================================
//
// Classifies nixpkgs top-level attributes by evaluating them with nix and
// generating val declarations. Most attrs are derivations; the rest are
// attrsets (sub-package-sets) or functions.

/// Options for the `gen-stubs pkgs` subcommand.
pub struct PkgsOptions {
    pub nixpkgs: Option<PathBuf>,
    /// Pre-computed classification JSON. When set, skip `nix eval` and read from this file.
    pub from_json: Option<PathBuf>,
    pub output: Option<PathBuf>,
    /// Maximum depth for recursing into sub-package-sets (e.g. llvmPackages, python3Packages).
    /// 0 = flat (no recursion), 1 = one level deep (default).
    pub max_depth: u32,
}

/// A classified nixpkgs attribute. The name is the map key (not stored here).
/// Non-derivation attrsets with `recurseForDerivations = true` get `children`
/// populated recursively up to the configured max depth.
#[derive(Debug, Deserialize)]
struct PkgClassification {
    #[serde(rename = "type")]
    nix_type: String,
    is_derivation: bool,
    #[serde(default)]
    children: Option<std::collections::BTreeMap<String, PkgClassification>>,
    /// When set, this package is an alias for another (e.g. `python3Packages`
    /// aliasing `python313Packages`). Detected via `dontRecurseIntoAttrs`
    /// + matching `builtins.attrNames`.
    #[serde(default)]
    alias_of: Option<String>,
}

/// Recursive tree of classified nixpkgs attributes.
type PkgTree = std::collections::BTreeMap<String, PkgClassification>;

/// Build the nix expression that recursively classifies nixpkgs attributes.
///
/// For each attr, we try to evaluate it and record:
///   - `type`: result of `builtins.typeOf`
///   - `is_derivation`: whether `value.type == "derivation"` (the conventional derivation marker)
///   - `children`: (optional) recursed sub-package-set contents
///
/// Non-derivation attrsets with `recurseForDerivations = true` are recursed into
/// up to `max_depth` levels. This is the same mechanism `nix search`, `nix-env -qa`,
/// and Hydra use to discover packages inside sub-package-sets like `llvmPackages`
/// and `python3Packages`.
///
/// Attrs that fail `tryEval` (broken or platform-restricted packages) are skipped.
fn build_pkgs_classify_expr(nixpkgs: &Option<PathBuf>, max_depth: u32) -> String {
    let nixpkgs_path = match nixpkgs {
        Some(ref p) => format!("{}", p.display()),
        None => "<nixpkgs>".to_string(),
    };
    format!(
        r#"let
  pkgs = import {nixpkgs_path} {{}};
  classifySet = depth: attrset:
    builtins.listToAttrs (builtins.concatMap (name:
      let v = builtins.tryEval (builtins.getAttr name attrset);
      in if !v.success then []
      else let
        ty = builtins.typeOf v.value;
        isDrv = (builtins.tryEval ((v.value.type or null) == "derivation")).value or false;
        shouldRecurse = !isDrv && ty == "set" && depth > 0
          && ((builtins.tryEval (v.value.recurseForDerivations or false)).value or false);
        children = if shouldRecurse then classifySet (depth - 1) v.value else null;
      in [{{
        inherit name;
        value = {{ type = ty; is_derivation = isDrv; }}
          // (if children != null then {{ inherit children; }} else {{}});
      }}]
    ) (builtins.attrNames attrset));

  # Alias detection: for non-recursed attrsets where recurseForDerivations is
  # explicitly false (the dontRecurseIntoAttrs signature), find a recursed
  # sibling with identical attrNames. Only runs at the top level.
  namesOf = s: builtins.filter (n: n != "recurseForDerivations") (builtins.attrNames s);

  detectAliases = tree: attrset:
    let
      recursedNames = builtins.filter (name:
        (tree.${{name}} or {{}}) ? children
      ) (builtins.attrNames tree);
    in builtins.mapAttrs (name: entry:
      if entry ? children || entry ? alias_of
         || entry.is_derivation || entry.type != "set" then entry
      else let
        val = builtins.tryEval (builtins.getAttr name attrset);
        hasExplicitFalse = val.success
          && val.value ? recurseForDerivations
          && val.value.recurseForDerivations == false;
      in if !hasExplicitFalse then entry
      else let
        candNames = namesOf val.value;
        match = builtins.filter (rName:
          namesOf (builtins.getAttr rName attrset) == candNames
        ) recursedNames;
      in if match == [] then entry
         else entry // {{ alias_of = builtins.head match; }}
    ) tree;

in detectAliases (classifySet {max_depth} pkgs) pkgs"#,
    )
}

/// Invoke `nix eval --json` to classify nixpkgs attributes recursively.
fn invoke_pkgs_classify(
    nixpkgs: &Option<PathBuf>,
    max_depth: u32,
) -> Result<PkgTree, Box<dyn std::error::Error>> {
    let expr = build_pkgs_classify_expr(nixpkgs, max_depth);
    let mut cmd = Command::new("nix");
    cmd.args(["eval", "--json", "--expr", &expr]);
    cmd.arg("--impure");

    eprintln!("Classifying nixpkgs attributes (max depth {max_depth}, this may take a while)...");
    let output = cmd.output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("nix eval failed:\n{}", stderr).into());
    }

    let tree: PkgTree = serde_json::from_slice(&output.stdout)?;
    Ok(tree)
}

/// Accumulates classification statistics during .tix emission.
#[derive(Default)]
struct PkgsStats {
    derivations: usize,
    attrsets: usize,
    functions: usize,
    sub_package_sets: usize,
    aliases: usize,
}

/// Capitalize a name for use as a type alias reference (first char uppercase,
/// rest unchanged). Module names like `python313Packages` become `Python313Packages`.
fn capitalize(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().to_string() + chars.as_str(),
    }
}

/// Generate a .tix file from a recursive tree of classified nixpkgs attributes.
///
/// Classification rules:
///   - `type == "set" && is_derivation` → `val name :: Derivation;`
///   - `type == "set" && !is_derivation` with children → `module name { ... }` (nested sub-package-set)
///   - `type == "set" && !is_derivation` without children → `val name :: { ... };` (opaque attrset)
///   - `type == "lambda"` → `val name :: a -> b;` (generic function, args unknowable without evaluation)
///   - Other types (string, list, etc.) → skip (rare, not useful as context args)
fn generate_pkgs_tix(tree: &PkgTree) -> String {
    let mut lines = vec![
        "# Auto-generated nixpkgs attribute stubs.".to_string(),
        "# Generated by: tix-cli gen-stubs pkgs".to_string(),
        "#".to_string(),
        "# Re-generate with: tix-cli gen-stubs pkgs -o <this-file>".to_string(),
        "#".to_string(),
        "# Load via --stubs to extend the built-in Pkgs type alias with all".to_string(),
        "# nixpkgs attributes. The module merges with the hand-curated".to_string(),
        "# `module pkgs` in the built-in stubs, so @callpackage picks these up".to_string(),
        "# automatically.".to_string(),
        String::new(),
        "module pkgs {".to_string(),
    ];

    let mut stats = PkgsStats::default();
    emit_pkg_tree(tree, 1, &mut lines, &mut stats);

    lines.push("}".to_string());

    eprintln!(
        "Classified {} attributes: {} derivations, {} attrsets, {} functions, {} sub-package-sets, {} aliases",
        stats.derivations + stats.attrsets + stats.functions + stats.sub_package_sets + stats.aliases,
        stats.derivations,
        stats.attrsets,
        stats.functions,
        stats.sub_package_sets,
        stats.aliases,
    );

    lines.push(String::new()); // trailing newline
    lines.join("\n")
}

/// Recursively emit val/module declarations for a package tree at the given
/// indentation level. Names that cannot be valid bare identifiers are emitted
/// as `val "quoted.name" :: ...;` rather than modules.
fn emit_pkg_tree(tree: &PkgTree, indent: usize, lines: &mut Vec<String>, stats: &mut PkgsStats) {
    let pad = "  ".repeat(indent);

    for (name, pkg) in tree {
        // `val` declarations require bare identifiers — the .tix grammar
        // doesn't support quoted names in val/module position. Skip names
        // that contain characters like `+`, `.`, etc.
        if needs_quoting(name) {
            continue;
        }

        // Alias reference: emit `val name :: AliasTarget;` where AliasTarget
        // is the capitalized module name (e.g. Python313Packages).
        if let Some(ref target) = pkg.alias_of {
            let alias_type = capitalize(target);
            stats.aliases += 1;
            lines.push(format!("{pad}val {name} :: {alias_type};"));
            continue;
        }

        match (pkg.nix_type.as_str(), pkg.is_derivation) {
            ("set", true) => {
                stats.derivations += 1;
                lines.push(format!("{pad}val {name} :: Derivation;"));
            }
            ("set", false) => {
                // Sub-package-sets with children become nested modules.
                if let Some(ref children) = pkg.children {
                    if !children.is_empty() {
                        stats.sub_package_sets += 1;
                        lines.push(format!("{pad}module {name} {{"));
                        emit_pkg_tree(children, indent + 1, lines, stats);
                        lines.push(format!("{pad}}}"));
                        continue;
                    }
                }
                stats.attrsets += 1;
                lines.push(format!("{pad}val {name} :: {{ ... }};"));
            }
            ("lambda", _) => {
                stats.functions += 1;
                lines.push(format!("{pad}val {name} :: a -> b;"));
            }
            _ => continue,
        }
    }
}

/// Run the `gen-stubs pkgs` subcommand.
pub fn run_pkgs(opts: PkgsOptions) -> Result<(), Box<dyn std::error::Error>> {
    let tree: PkgTree = match opts.from_json {
        Some(ref path) => {
            let data = std::fs::read(path)
                .map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
            serde_json::from_slice(&data)
                .map_err(|e| format!("failed to parse JSON from {}: {}", path.display(), e))?
        }
        None => invoke_pkgs_classify(&opts.nixpkgs, opts.max_depth)?,
    };
    let tix_content = generate_pkgs_tix(&tree);
    write_generated_stubs(&tix_content, opts.output.as_ref(), "pkgs")
}

/// Validate and write generated .tix content to a file or stdout.
fn write_generated_stubs(
    tix_content: &str,
    output: Option<&PathBuf>,
    label: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // Validate the generated .tix output parses correctly.
    if let Err(e) = comment_parser::parse_tix_file(tix_content) {
        eprintln!(
            "Warning: generated .tix file has parse errors (please report this bug): {}",
            e
        );
    }

    match output {
        Some(path) => {
            // Ensure parent directory exists.
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(path, tix_content)?;
            eprintln!("Wrote {} option stubs to {}", label, path.display());
        }
        None => {
            std::io::stdout().write_all(tix_content.as_bytes())?;
        }
    }

    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    // -------------------------------------------------------------------------
    // JSON deserialization
    // -------------------------------------------------------------------------

    #[test]
    fn deserialize_primitive_option() {
        let json = r#"{"_isOption": true, "typeInfo": {"type": "primitive", "value": "bool"}}"#;
        let node: OptionNode = serde_json::from_str(json).unwrap();
        match node {
            OptionNode::Option(leaf) => {
                assert!(leaf._is_option);
                assert_eq!(
                    leaf.type_info,
                    NixosTypeInfo::Primitive {
                        value: "bool".into()
                    }
                );
            }
            _ => panic!("expected Option"),
        }
    }

    #[test]
    fn deserialize_namespace() {
        let json = r#"{
            "_isOption": false,
            "children": {
                "enable": {"_isOption": true, "typeInfo": {"type": "primitive", "value": "bool"}}
            }
        }"#;
        let node: OptionNode = serde_json::from_str(json).unwrap();
        match node {
            OptionNode::Namespace(ns) => {
                assert!(!ns._is_option);
                assert!(ns.children.contains_key("enable"));
            }
            _ => panic!("expected Namespace"),
        }
    }

    #[test]
    fn deserialize_list_type() {
        let json = r#"{"type": "list", "elem": {"type": "primitive", "value": "string"}}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        assert_eq!(
            ty,
            NixosTypeInfo::List {
                elem: Box::new(NixosTypeInfo::Primitive {
                    value: "string".into()
                })
            }
        );
    }

    #[test]
    fn deserialize_attrs_of() {
        let json = r#"{"type": "attrsOf", "elem": {"type": "primitive", "value": "int"}}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        assert_eq!(
            ty,
            NixosTypeInfo::AttrsOf {
                elem: Box::new(NixosTypeInfo::Primitive {
                    value: "int".into()
                })
            }
        );
    }

    #[test]
    fn deserialize_null_or() {
        let json = r#"{"type": "nullOr", "elem": {"type": "primitive", "value": "string"}}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        assert_eq!(
            ty,
            NixosTypeInfo::NullOr {
                elem: Box::new(NixosTypeInfo::Primitive {
                    value: "string".into()
                })
            }
        );
    }

    #[test]
    fn deserialize_union() {
        let json = r#"{"type": "union", "members": [
            {"type": "primitive", "value": "string"},
            {"type": "primitive", "value": "int"}
        ]}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        match ty {
            NixosTypeInfo::Union { members } => assert_eq!(members.len(), 2),
            _ => panic!("expected Union"),
        }
    }

    #[test]
    fn deserialize_submodule() {
        let json = r#"{"type": "submodule", "options": {
            "port": {"_isOption": true, "typeInfo": {"type": "primitive", "value": "int"}}
        }}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        match ty {
            NixosTypeInfo::Submodule { options } => {
                assert!(options.contains_key("port"));
            }
            _ => panic!("expected Submodule"),
        }
    }

    #[test]
    fn deserialize_function() {
        let json = r#"{"type": "function", "result": {"type": "primitive", "value": "bool"}}"#;
        let ty: NixosTypeInfo = serde_json::from_str(json).unwrap();
        assert_eq!(
            ty,
            NixosTypeInfo::Function {
                result: Box::new(NixosTypeInfo::Primitive {
                    value: "bool".into()
                })
            }
        );
    }

    #[test]
    fn deserialize_enum_and_anything() {
        let _: NixosTypeInfo = serde_json::from_str(r#"{"type": "enum"}"#).unwrap();
        let _: NixosTypeInfo = serde_json::from_str(r#"{"type": "anything"}"#).unwrap();
        let _: NixosTypeInfo = serde_json::from_str(r#"{"type": "package"}"#).unwrap();
    }

    // -------------------------------------------------------------------------
    // type_to_tix conversion
    // -------------------------------------------------------------------------

    #[test]
    fn tix_primitives() {
        assert_eq!(
            type_to_tix(&NixosTypeInfo::Primitive {
                value: "bool".into()
            }),
            "bool"
        );
        assert_eq!(
            type_to_tix(&NixosTypeInfo::Primitive {
                value: "string".into()
            }),
            "string"
        );
        assert_eq!(
            type_to_tix(&NixosTypeInfo::Primitive {
                value: "int".into()
            }),
            "int"
        );
        assert_eq!(
            type_to_tix(&NixosTypeInfo::Primitive {
                value: "float".into()
            }),
            "float"
        );
        assert_eq!(
            type_to_tix(&NixosTypeInfo::Primitive {
                value: "path".into()
            }),
            "path"
        );
    }

    #[test]
    fn tix_list() {
        let ty = NixosTypeInfo::List {
            elem: Box::new(NixosTypeInfo::Primitive {
                value: "string".into(),
            }),
        };
        assert_eq!(type_to_tix(&ty), "[string]");
    }

    #[test]
    fn tix_attrs_of() {
        let ty = NixosTypeInfo::AttrsOf {
            elem: Box::new(NixosTypeInfo::Primitive {
                value: "int".into(),
            }),
        };
        assert_eq!(type_to_tix(&ty), "{ _: int }");
    }

    #[test]
    fn tix_null_or() {
        let ty = NixosTypeInfo::NullOr {
            elem: Box::new(NixosTypeInfo::Primitive {
                value: "string".into(),
            }),
        };
        assert_eq!(type_to_tix(&ty), "string | null");
    }

    #[test]
    fn tix_null_or_parenthesization() {
        // nullOr (listOf string) inside a list — the `[...]` brackets already
        // delimit, so no extra parens needed around the inner union.
        let inner = NixosTypeInfo::NullOr {
            elem: Box::new(NixosTypeInfo::List {
                elem: Box::new(NixosTypeInfo::Primitive {
                    value: "string".into(),
                }),
            }),
        };
        let outer = NixosTypeInfo::List {
            elem: Box::new(inner),
        };
        assert_eq!(type_to_tix(&outer), "[[string] | null]");
    }

    #[test]
    fn tix_null_or_in_arrow_needs_parens() {
        // `nullOr string -> bool` should not parenthesize since -> binds tighter
        // than |. But `(nullOr string) -> bool` as a *param* needs parens.
        // Test: nullOr as the *result* of functionTo — no parens needed.
        let ty = NixosTypeInfo::Function {
            result: Box::new(NixosTypeInfo::NullOr {
                elem: Box::new(NixosTypeInfo::Primitive {
                    value: "string".into(),
                }),
            }),
        };
        assert_eq!(type_to_tix(&ty), "{ ... } -> string | null");
    }

    #[test]
    fn tix_union() {
        let ty = NixosTypeInfo::Union {
            members: vec![
                NixosTypeInfo::Primitive {
                    value: "string".into(),
                },
                NixosTypeInfo::Primitive {
                    value: "int".into(),
                },
            ],
        };
        assert_eq!(type_to_tix(&ty), "string | int");
    }

    #[test]
    fn tix_enum() {
        assert_eq!(type_to_tix(&NixosTypeInfo::Enum), "string");
    }

    #[test]
    fn tix_package() {
        assert_eq!(type_to_tix(&NixosTypeInfo::Package), "Derivation");
    }

    #[test]
    fn tix_anything() {
        assert_eq!(type_to_tix(&NixosTypeInfo::Anything), "{ ... }");
    }

    #[test]
    fn tix_function() {
        let ty = NixosTypeInfo::Function {
            result: Box::new(NixosTypeInfo::Primitive {
                value: "bool".into(),
            }),
        };
        assert_eq!(type_to_tix(&ty), "{ ... } -> bool");
    }

    #[test]
    fn tix_submodule() {
        let mut opts = BTreeMap::new();
        opts.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: None,
            }),
        );
        let ty = NixosTypeInfo::Submodule { options: opts };
        let result = type_to_tix(&ty);
        assert!(result.contains("enable: bool"));
        assert!(result.contains("..."));
    }

    // -------------------------------------------------------------------------
    // options_to_attrset_ty
    // -------------------------------------------------------------------------

    #[test]
    fn empty_options() {
        let opts = BTreeMap::new();
        assert_eq!(options_to_attrset_ty(&opts, 0), "{ ... }");
    }

    #[test]
    fn flat_options() {
        let mut opts = BTreeMap::new();
        opts.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: None,
            }),
        );
        opts.insert(
            "port".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "int".into(),
                },
                description: None,
            }),
        );
        let result = options_to_attrset_ty(&opts, 0);
        assert!(result.contains("enable: bool"));
        assert!(result.contains("port: int"));
        assert!(result.contains("..."));
    }

    #[test]
    fn nested_namespace() {
        let mut inner = BTreeMap::new();
        inner.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: None,
            }),
        );
        let mut outer = BTreeMap::new();
        outer.insert(
            "services".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: inner,
            }),
        );
        let result = options_to_attrset_ty(&outer, 0);
        assert!(result.contains("services:"));
        assert!(result.contains("enable: bool"));
    }

    // -------------------------------------------------------------------------
    // Round-trip: generate → parse
    // -------------------------------------------------------------------------

    #[test]
    fn round_trip_generated_tix_parses() {
        let mut services = BTreeMap::new();
        let mut openssh = BTreeMap::new();
        openssh.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: None,
            }),
        );
        openssh.insert(
            "ports".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::List {
                    elem: Box::new(NixosTypeInfo::Primitive {
                        value: "int".into(),
                    }),
                },
                description: None,
            }),
        );
        services.insert(
            "openssh".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: openssh,
            }),
        );

        let mut tree = BTreeMap::new();
        tree.insert(
            "services".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: services,
            }),
        );
        tree.insert(
            "networking".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: {
                    let mut m = BTreeMap::new();
                    m.insert(
                        "hostName".to_string(),
                        OptionNode::Option(OptionLeaf {
                            _is_option: true,
                            type_info: NixosTypeInfo::Primitive {
                                value: "string".into(),
                            },
                            description: None,
                        }),
                    );
                    m.insert(
                        "firewall".to_string(),
                        OptionNode::Namespace(NamespaceNode {
                            _is_option: false,
                            children: {
                                let mut fw = BTreeMap::new();
                                fw.insert(
                                    "enable".to_string(),
                                    OptionNode::Option(OptionLeaf {
                                        _is_option: true,
                                        type_info: NixosTypeInfo::Primitive {
                                            value: "bool".into(),
                                        },
                                        description: None,
                                    }),
                                );
                                fw.insert(
                                    "allowedTCPPorts".to_string(),
                                    OptionNode::Option(OptionLeaf {
                                        _is_option: true,
                                        type_info: NixosTypeInfo::List {
                                            elem: Box::new(NixosTypeInfo::Primitive {
                                                value: "int".into(),
                                            }),
                                        },
                                        description: None,
                                    }),
                                );
                                fw
                            },
                        }),
                    );
                    m
                },
            }),
        );

        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);

        // The generated file must parse successfully.
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Generated .tix failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    #[test]
    fn round_trip_with_complex_types() {
        let mut tree = BTreeMap::new();
        tree.insert(
            "nullableStr".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::NullOr {
                    elem: Box::new(NixosTypeInfo::Primitive {
                        value: "string".into(),
                    }),
                },
                description: None,
            }),
        );
        tree.insert(
            "packages".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::List {
                    elem: Box::new(NixosTypeInfo::Package),
                },
                description: None,
            }),
        );
        tree.insert(
            "extraConfig".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::AttrsOf {
                    elem: Box::new(NixosTypeInfo::Primitive {
                        value: "string".into(),
                    }),
                },
                description: None,
            }),
        );

        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Generated .tix failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    #[test]
    fn round_trip_with_hyphenated_names() {
        let mut tree = BTreeMap::new();
        let mut boot = BTreeMap::new();
        boot.insert(
            "systemd-boot".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: {
                    let mut m = BTreeMap::new();
                    m.insert(
                        "enable".to_string(),
                        OptionNode::Option(OptionLeaf {
                            _is_option: true,
                            type_info: NixosTypeInfo::Primitive {
                                value: "bool".into(),
                            },
                            description: None,
                        }),
                    );
                    m
                },
            }),
        );
        tree.insert(
            "boot".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: boot,
            }),
        );

        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);
        assert!(tix_content.contains("systemd-boot"));
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Generated .tix with hyphens failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    // -------------------------------------------------------------------------
    // Integration test (requires nix, run with `cargo test -- --ignored`)
    // -------------------------------------------------------------------------

    #[test]
    #[ignore]
    fn integration_nixos_eval() {
        let opts = NixosOptions {
            common: CommonOptions {
                nixpkgs: None,
                flake: None,
                from_json: None,
                output: None,
                max_depth: 4, // shallow for speed
                descriptions: false,
            },
            hostname: None,
        };
        let tree = invoke_nix_eval(&opts).expect("nix eval should succeed");
        assert!(!tree.is_empty(), "option tree should not be empty");

        // The tree should contain common top-level namespaces.
        assert!(
            tree.contains_key("services") || tree.contains_key("networking"),
            "expected common NixOS option namespaces"
        );

        // Generate .tix and verify it parses.
        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            // Write to a temp file for debugging.
            let tmp = std::env::temp_dir().join("tix-nixos-stubs-debug.tix");
            let _ = std::fs::write(&tmp, &tix_content);
            panic!(
                "Integration: generated .tix failed to parse (saved to {}):\n{}",
                tmp.display(),
                e
            );
        });
    }

    #[test]
    fn round_trip_home_manager_kind() {
        let mut tree = BTreeMap::new();
        tree.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: None,
            }),
        );
        tree.insert(
            "home".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: {
                    let mut m = BTreeMap::new();
                    m.insert(
                        "username".to_string(),
                        OptionNode::Option(OptionLeaf {
                            _is_option: true,
                            type_info: NixosTypeInfo::Primitive {
                                value: "string".into(),
                            },
                            description: None,
                        }),
                    );
                    m.insert(
                        "homeDirectory".to_string(),
                        OptionNode::Option(OptionLeaf {
                            _is_option: true,
                            type_info: NixosTypeInfo::Primitive {
                                value: "path".into(),
                            },
                            description: None,
                        }),
                    );
                    m.insert(
                        "packages".to_string(),
                        OptionNode::Option(OptionLeaf {
                            _is_option: true,
                            type_info: NixosTypeInfo::List {
                                elem: Box::new(NixosTypeInfo::Package),
                            },
                            description: None,
                        }),
                    );
                    m
                },
            }),
        );

        let tix_content = generate_tix_file(&tree, &StubKind::HomeManager);

        // Should contain HomeManagerConfig type and context val declarations.
        assert!(tix_content.contains("type HomeManagerConfig"));
        assert!(tix_content.contains("val config :: HomeManagerConfig;"));
        assert!(tix_content.contains("val lib :: Lib;"));
        assert!(tix_content.contains("val pkgs :: Pkgs;"));
        assert!(tix_content.contains("val osConfig :: { ... };"));

        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "HM generated .tix failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    #[test]
    #[ignore]
    fn integration_home_manager_eval() {
        let opts = HomeManagerOptions {
            common: CommonOptions {
                nixpkgs: None,
                flake: None,
                from_json: None,
                output: None,
                max_depth: 3, // shallow for speed
                descriptions: false,
            },
            home_manager: None,
            username: None,
        };
        let tree = invoke_hm_nix_eval(&opts).expect("nix eval should succeed");
        assert!(!tree.is_empty(), "option tree should not be empty");

        // HM option tree should contain common top-level namespaces.
        assert!(
            tree.contains_key("home") || tree.contains_key("programs"),
            "expected common Home Manager option namespaces, got: {:?}",
            tree.keys().collect::<Vec<_>>()
        );

        let tix_content = generate_tix_file(&tree, &StubKind::HomeManager);
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            let tmp = std::env::temp_dir().join("tix-hm-stubs-debug.tix");
            let _ = std::fs::write(&tmp, &tix_content);
            panic!(
                "Integration: generated HM .tix failed to parse (saved to {}):\n{}",
                tmp.display(),
                e
            );
        });
    }

    // -------------------------------------------------------------------------
    // Field name quoting
    // -------------------------------------------------------------------------

    #[test]
    fn needs_quoting_plain_idents() {
        assert!(!needs_quoting("enable"));
        assert!(!needs_quoting("hostName"));
        assert!(!needs_quoting("systemd-boot"));
        assert!(!needs_quoting("2bwm"));
        assert!(!needs_quoting("_1password"));
    }

    #[test]
    fn needs_quoting_dotted_names() {
        assert!(needs_quoting("net.core.rmem_max"));
        assert!(needs_quoting("com.apple.controlcenter"));
        assert!(needs_quoting("NSGlobalDomain.AppleShowAllExtensions"));
    }

    #[test]
    fn needs_quoting_edge_cases() {
        assert!(needs_quoting(""));
        assert!(needs_quoting("_")); // reserved for dyn_field
    }

    #[test]
    fn round_trip_with_dotted_names() {
        let mut sysctl = BTreeMap::new();
        sysctl.insert(
            "net.core.rmem_max".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "string".into(),
                },
                description: None,
            }),
        );

        let mut tree = BTreeMap::new();
        tree.insert(
            "sysctl".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: sysctl,
            }),
        );

        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);
        assert!(tix_content.contains(r#""net.core.rmem_max": string"#));

        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Dotted-name .tix failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    // -------------------------------------------------------------------------
    // Doc comment generation
    // -------------------------------------------------------------------------

    #[test]
    fn doc_comments_emitted_with_descriptions() {
        let mut tree = BTreeMap::new();
        tree.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: Some("Whether to enable the service.".to_string()),
            }),
        );
        tree.insert(
            "port".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "int".into(),
                },
                description: None,
            }),
        );

        let tix_content = generate_tix_file_with_docs(&tree, &StubKind::Nixos, true);

        // The doc comment should appear before the `enable` field.
        assert!(
            tix_content.contains("## Whether to enable the service."),
            "Expected doc comment in output:\n{tix_content}"
        );
        // The `port` field should NOT have a doc comment.
        assert!(
            !tix_content.contains("## \n  port"),
            "Unexpected empty doc comment for port:\n{tix_content}"
        );

        // The output should still parse correctly with doc comments.
        comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Doc comment .tix failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });
    }

    #[test]
    fn doc_comments_round_trip_with_field_docs() {
        let mut tree = BTreeMap::new();
        let mut services = BTreeMap::new();
        services.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: Some("Whether to enable OpenSSH.".to_string()),
            }),
        );
        tree.insert(
            "services".to_string(),
            OptionNode::Namespace(NamespaceNode {
                _is_option: false,
                children: services,
            }),
        );

        let tix_content = generate_tix_file_with_docs(&tree, &StubKind::Nixos, true);

        // Parse the generated file.
        let file = comment_parser::parse_tix_file(&tix_content).unwrap_or_else(|e| {
            panic!(
                "Generated .tix with docs failed to parse:\n{}\n\nError: {}",
                tix_content, e
            );
        });

        // The field doc should be collected during parsing.
        assert!(
            !file.field_docs.is_empty(),
            "Expected field docs to be collected from generated output"
        );

        // Load into a registry and verify doc index is populated.
        let mut registry = lang_check::aliases::TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let path = vec![
            smol_str::SmolStr::from("services"),
            smol_str::SmolStr::from("enable"),
        ];
        assert_eq!(
            registry
                .docs
                .field_doc("NixosConfig", &path)
                .map(|s| s.as_str()),
            Some("Whether to enable OpenSSH."),
        );
    }

    #[test]
    fn no_doc_comments_without_flag() {
        let mut tree = BTreeMap::new();
        tree.insert(
            "enable".to_string(),
            OptionNode::Option(OptionLeaf {
                _is_option: true,
                type_info: NixosTypeInfo::Primitive {
                    value: "bool".into(),
                },
                description: Some("Whether to enable.".to_string()),
            }),
        );

        // Without descriptions flag.
        let tix_content = generate_tix_file(&tree, &StubKind::Nixos);
        assert!(
            !tix_content.contains("##"),
            "Should not contain doc comments without flag:\n{tix_content}"
        );
    }

    // -------------------------------------------------------------------------
    // gen-stubs pkgs
    // -------------------------------------------------------------------------

    /// Helper to build a flat PkgTree entry (no children).
    fn pkg(nix_type: &str, is_derivation: bool) -> PkgClassification {
        PkgClassification {
            nix_type: nix_type.to_string(),
            is_derivation,
            children: None,
            alias_of: None,
        }
    }

    /// Helper to build a sub-package-set entry with children.
    fn pkg_with_children(children: PkgTree) -> PkgClassification {
        PkgClassification {
            nix_type: "set".to_string(),
            is_derivation: false,
            children: Some(children),
            alias_of: None,
        }
    }

    /// Helper to build an alias entry pointing at another package set.
    fn pkg_alias(target: &str) -> PkgClassification {
        PkgClassification {
            nix_type: "set".to_string(),
            is_derivation: false,
            children: None,
            alias_of: Some(target.to_string()),
        }
    }

    #[test]
    fn generate_pkgs_tix_derivations() {
        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("coreutils".to_string(), pkg("set", true));
        let tix = generate_pkgs_tix(&tree);
        assert!(tix.contains("val hello :: Derivation;"));
        assert!(tix.contains("val coreutils :: Derivation;"));
    }

    #[test]
    fn generate_pkgs_tix_attrsets_and_functions() {
        let mut tree = PkgTree::new();
        tree.insert("xorg".to_string(), pkg("set", false));
        tree.insert("callPackage".to_string(), pkg("lambda", false));
        let tix = generate_pkgs_tix(&tree);
        assert!(tix.contains("val xorg :: { ... };"));
        assert!(tix.contains("val callPackage :: a -> b;"));
    }

    #[test]
    fn generate_pkgs_tix_skips_other_types() {
        let mut tree = PkgTree::new();
        tree.insert("version".to_string(), pkg("string", false));
        tree.insert("hello".to_string(), pkg("set", true));
        let tix = generate_pkgs_tix(&tree);
        assert!(!tix.contains("val version"));
        assert!(tix.contains("val hello :: Derivation;"));
    }

    #[test]
    fn generate_pkgs_tix_wrapped_in_module() {
        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        let tix = generate_pkgs_tix(&tree);
        assert!(
            tix.contains("module pkgs {"),
            "should wrap vals in module pkgs"
        );
        assert!(tix.contains('}'), "module should be closed");
    }

    #[test]
    fn generate_pkgs_tix_merges_with_builtins() {
        // Verify that loading generated pkgs stubs alongside the built-in stubs
        // merges into the Pkgs alias, giving both hand-curated and generated fields.
        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        let tix = generate_pkgs_tix(&tree);
        let file = comment_parser::parse_tix_file(&tix).expect("should parse");

        let mut registry = lang_check::aliases::TypeAliasRegistry::with_builtins();
        registry.load_tix_file(&file);

        let pkgs_ty = registry.get("Pkgs").expect("Pkgs alias should exist");
        match pkgs_ty {
            comment_parser::ParsedTy::AttrSet(attr) => {
                // Hand-curated field from built-in stubs.
                assert!(
                    attr.fields.contains_key("stdenv"),
                    "should keep built-in stdenv"
                );
                // Generated field from the pkgs stubs.
                assert!(
                    attr.fields.contains_key("hello"),
                    "should have generated hello"
                );
            }
            other => panic!("expected AttrSet for Pkgs, got: {other:?}"),
        }
    }

    #[test]
    fn generate_pkgs_tix_round_trip_parses() {
        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("pythonPackages".to_string(), pkg("set", false));
        tree.insert("writeText".to_string(), pkg("lambda", false));
        let tix = generate_pkgs_tix(&tree);
        comment_parser::parse_tix_file(&tix).unwrap_or_else(|e| {
            panic!(
                "Generated pkgs .tix failed to parse:\n{}\n\nError: {}",
                tix, e
            );
        });
    }

    // -------------------------------------------------------------------------
    // gen-stubs pkgs: recursive sub-package-sets
    // -------------------------------------------------------------------------

    #[test]
    fn deserialize_recursive_pkg_tree() {
        let json = r#"{
            "hello": { "type": "set", "is_derivation": true },
            "llvmPackages": {
                "type": "set", "is_derivation": false,
                "children": {
                    "clang": { "type": "set", "is_derivation": true },
                    "llvm": { "type": "set", "is_derivation": true }
                }
            }
        }"#;
        let tree: PkgTree = serde_json::from_str(json).unwrap();
        assert_eq!(tree.len(), 2);
        assert!(tree["hello"].is_derivation);
        let children = tree["llvmPackages"].children.as_ref().unwrap();
        assert_eq!(children.len(), 2);
        assert!(children["clang"].is_derivation);
        assert!(children["llvm"].is_derivation);
    }

    #[test]
    fn generate_pkgs_tix_nested_modules() {
        let mut children = PkgTree::new();
        children.insert("clang".to_string(), pkg("set", true));
        children.insert("llvm".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("llvmPackages".to_string(), pkg_with_children(children));

        let tix = generate_pkgs_tix(&tree);
        assert!(tix.contains("val hello :: Derivation;"));
        assert!(
            tix.contains("module llvmPackages {"),
            "sub-package-set should become nested module"
        );
        assert!(
            tix.contains("val clang :: Derivation;"),
            "children should be emitted inside nested module"
        );
        assert!(tix.contains("val llvm :: Derivation;"));
    }

    #[test]
    fn generate_pkgs_tix_nested_round_trip_parses() {
        let mut children = PkgTree::new();
        children.insert("clang".to_string(), pkg("set", true));
        children.insert("buildTools".to_string(), pkg("lambda", false));

        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("llvmPackages".to_string(), pkg_with_children(children));
        tree.insert("writeText".to_string(), pkg("lambda", false));

        let tix = generate_pkgs_tix(&tree);
        comment_parser::parse_tix_file(&tix).unwrap_or_else(|e| {
            panic!(
                "Generated nested pkgs .tix failed to parse:\n{}\n\nError: {}",
                tix, e
            );
        });
    }

    #[test]
    fn generate_pkgs_tix_nested_merges_with_builtins() {
        // Nested modules should merge into the Pkgs alias alongside built-in stubs.
        let mut children = PkgTree::new();
        children.insert("clang".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("llvmPackages".to_string(), pkg_with_children(children));

        let tix = generate_pkgs_tix(&tree);
        let file = comment_parser::parse_tix_file(&tix).expect("should parse");

        let mut registry = lang_check::aliases::TypeAliasRegistry::with_builtins();
        registry.load_tix_file(&file);

        let pkgs_ty = registry.get("Pkgs").expect("Pkgs alias should exist");
        match pkgs_ty {
            comment_parser::ParsedTy::AttrSet(attr) => {
                assert!(
                    attr.fields.contains_key("hello"),
                    "should have generated hello"
                );
                assert!(
                    attr.fields.contains_key("llvmPackages"),
                    "should have generated llvmPackages"
                );
            }
            other => panic!("expected AttrSet for Pkgs, got: {other:?}"),
        }
    }

    #[test]
    fn generate_pkgs_tix_empty_children_becomes_val() {
        // An attrset with empty children should not become a module.
        let mut tree = PkgTree::new();
        tree.insert("emptySet".to_string(), pkg_with_children(PkgTree::new()));
        let tix = generate_pkgs_tix(&tree);
        assert!(
            tix.contains("val emptySet :: { ... };"),
            "empty children should fall back to val: {tix}"
        );
        assert!(
            !tix.contains("module emptySet"),
            "should not emit module for empty children"
        );
    }

    #[test]
    fn generate_pkgs_tix_invalid_names_skipped() {
        // Names requiring quoting (dots, `+`, etc.) can't be used in val/module
        // declarations — the .tix grammar only supports bare identifiers there.
        // These names are skipped entirely.
        let mut children = PkgTree::new();
        children.insert("inner".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("name.with.dots".to_string(), pkg_with_children(children));
        tree.insert("m+".to_string(), pkg("set", true));
        tree.insert("hello".to_string(), pkg("set", true));
        let tix = generate_pkgs_tix(&tree);
        assert!(
            !tix.contains("name.with.dots"),
            "dotted name should be skipped: {tix}"
        );
        assert!(!tix.contains("m+"), "m+ should be skipped: {tix}");
        assert!(tix.contains("val hello :: Derivation;"));
        comment_parser::parse_tix_file(&tix).unwrap_or_else(|e| {
            panic!("Skipped-names pkgs .tix failed to parse:\n{tix}\n\nError: {e}");
        });
    }

    // -------------------------------------------------------------------------
    // gen-stubs pkgs: alias detection
    // -------------------------------------------------------------------------

    #[test]
    fn deserialize_alias_of_field() {
        let json = r#"{
            "python3Packages": {
                "type": "set", "is_derivation": false,
                "alias_of": "python313Packages"
            },
            "python313Packages": {
                "type": "set", "is_derivation": false,
                "children": {
                    "numpy": { "type": "set", "is_derivation": true }
                }
            }
        }"#;
        let tree: PkgTree = serde_json::from_str(json).unwrap();
        assert_eq!(
            tree["python3Packages"].alias_of.as_deref(),
            Some("python313Packages")
        );
        assert!(tree["python313Packages"].children.is_some());
        assert!(tree["python313Packages"].alias_of.is_none());
    }

    #[test]
    fn generate_pkgs_tix_alias_emits_type_ref() {
        let mut children = PkgTree::new();
        children.insert("numpy".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("python313Packages".to_string(), pkg_with_children(children));
        tree.insert(
            "python3Packages".to_string(),
            pkg_alias("python313Packages"),
        );

        let tix = generate_pkgs_tix(&tree);
        assert!(
            tix.contains("module python313Packages {"),
            "should emit module for recursed set: {tix}"
        );
        assert!(
            tix.contains("val python3Packages :: Python313Packages;"),
            "alias should reference capitalized module type: {tix}"
        );
        assert!(
            !tix.contains("module python3Packages"),
            "alias should not become a module: {tix}"
        );
    }

    #[test]
    fn generate_pkgs_tix_alias_round_trip_parses() {
        let mut children = PkgTree::new();
        children.insert("numpy".to_string(), pkg("set", true));
        children.insert("pandas".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("hello".to_string(), pkg("set", true));
        tree.insert("python313Packages".to_string(), pkg_with_children(children));
        tree.insert(
            "python3Packages".to_string(),
            pkg_alias("python313Packages"),
        );

        let tix = generate_pkgs_tix(&tree);
        comment_parser::parse_tix_file(&tix).unwrap_or_else(|e| {
            panic!("Alias pkgs .tix failed to parse:\n{tix}\n\nError: {e}");
        });
    }

    #[test]
    fn generate_pkgs_tix_alias_resolves_in_registry() {
        // Verify that the alias type reference can be resolved through
        // the TypeAliasRegistry after loading the generated stubs.
        let mut children = PkgTree::new();
        children.insert("numpy".to_string(), pkg("set", true));

        let mut tree = PkgTree::new();
        tree.insert("python313Packages".to_string(), pkg_with_children(children));
        tree.insert(
            "python3Packages".to_string(),
            pkg_alias("python313Packages"),
        );

        let tix = generate_pkgs_tix(&tree);
        let file = comment_parser::parse_tix_file(&tix).expect("should parse");

        let mut registry = lang_check::aliases::TypeAliasRegistry::with_builtins();
        registry.load_tix_file(&file);

        let pkgs_ty = registry.get("Pkgs").expect("Pkgs alias should exist");
        match pkgs_ty {
            comment_parser::ParsedTy::AttrSet(attr) => {
                // The alias should resolve to a Reference to the module type.
                match attr.fields.get("python3Packages") {
                    Some(comment_parser::ParsedTyRef(ty)) => match ty.as_ref() {
                        comment_parser::ParsedTy::TyVar(
                            comment_parser::TypeVarValue::Reference(name),
                        ) => {
                            assert_eq!(
                                name.as_str(),
                                "Python313Packages",
                                "alias val should reference the capitalized module type"
                            );
                        }
                        other => panic!("expected Reference for python3Packages, got: {other:?}"),
                    },
                    other => panic!("expected ParsedTyRef for python3Packages, got: {other:?}"),
                }
                // The module target itself should exist as a type alias.
                assert!(
                    registry.get("Python313Packages").is_some(),
                    "Python313Packages type alias should exist from module declaration"
                );
            }
            other => panic!("expected AttrSet for Pkgs, got: {other:?}"),
        }
    }

    #[test]
    fn capitalize_helper() {
        assert_eq!(capitalize("python313Packages"), "Python313Packages");
        assert_eq!(capitalize("llvmPackages"), "LlvmPackages");
        assert_eq!(capitalize(""), "");
        assert_eq!(capitalize("a"), "A");
    }
}
