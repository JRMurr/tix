// ==============================================================================
// textDocument/hover — show inferred type on hover
// ==============================================================================
//
// Converts the cursor position to a byte offset, finds the smallest syntax
// node at that offset, maps it to an ExprId or NameId via the source map,
// then looks up the inferred type. If stub docs are available for the hovered
// name or field, they're appended below the type.

use lang_ast::nameres::ResolveResult;
use lang_ast::{AstPtr, Expr, NameKind};
use lang_check::aliases::DocIndex;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Hover, HoverContents, MarkupContent, MarkupKind, Position, Range};

use crate::state::FileSnapshot;

/// Whether this name kind represents a parameter (genuine polymorphism).
/// Param/PatField keep letter names; all others use `?` for unknowns.
fn is_param_kind(kind: NameKind) -> bool {
    matches!(kind, NameKind::Param | NameKind::PatField)
}

/// Try to produce hover information for the given cursor position.
pub fn hover(
    analysis: &FileSnapshot,
    pos: Position,
    root: &rnix::Root,
    docs: &DocIndex,
) -> Option<Hover> {
    let inference = analysis.inference_result()?;
    let offset = analysis.syntax.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    // Walk up from the token to find the smallest node that has a source map entry.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Check for a name at this node first (shows the binding's type).
        if let Some(name_id) = analysis.syntax.source_map.name_for_node(ptr) {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                let name_text = &analysis.syntax.module[name_id].text;
                let range = analysis.syntax.line_index.range(node.text_range());

                // Look up doc comment for this name from stubs.
                // First try decl-level docs (global vals, type aliases).
                let mut doc = docs.decl_doc(name_text.as_str()).map(|d| d.to_string());

                // If no decl doc, check if this name is an attrpath key inside
                // a NixOS module body — use field-level docs from the config type.
                if doc.is_none() {
                    doc = try_attrpath_key_field_doc(analysis, &token, docs);
                }

                // Param/PatField: keep letter names (genuine polymorphism).
                // All other bindings: replace single-occurrence TyVars with `?`.
                let kind = analysis.syntax.module[name_id].kind;
                let ty_str = if is_param_kind(kind) {
                    format!("{ty}")
                } else {
                    format!("{}", ty.normalize_replacing_unknown())
                };

                return Some(make_hover(
                    format!("{name_text} :: {ty_str}"),
                    doc.as_deref(),
                    range,
                ));
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.syntax.source_map.expr_for_node(ptr) {
            // Attrpath idents are lowered to Literal(String) with their own
            // source_map entries, so the walk-up finds them before the parent
            // Select. Skip these so we land on the Select node instead, which
            // has the correct field type and docs.
            if is_select_attrpath(&node) {
                node = node.parent()?;
                continue;
            }

            if let Some(ty) = inference.expr_ty_map.get(expr_id) {
                let range = analysis.syntax.line_index.range(node.text_range());

                // Determine normalization mode: if this expression is a
                // Reference to a Param/PatField, use regular normalization
                // (letters for genuine polymorphism). Otherwise use
                // unknown-replacing normalization (`?` for unknowns).
                let is_param_ref = match &analysis.syntax.module[expr_id] {
                    Expr::Reference(_) => analysis
                        .syntax
                        .name_res
                        .get(expr_id)
                        .and_then(|r| match r {
                            ResolveResult::Definition(nid) => Some(*nid),
                            _ => None,
                        })
                        .map(|nid| is_param_kind(analysis.syntax.module[nid].kind))
                        .unwrap_or(false),
                    _ => false,
                };
                let ty_display = if is_param_ref {
                    ty.normalize_vars()
                } else {
                    ty.normalize_replacing_unknown()
                };

                // For Reference expressions (variable uses), look up decl_doc
                // by the referenced name. This surfaces docs for global vals
                // from stubs (e.g. hovering on `mkDerivation` shows its doc).
                if let Expr::Reference(ref_name) = &analysis.syntax.module[expr_id] {
                    let doc = docs.decl_doc(ref_name.as_str());
                    return Some(make_hover(
                        format!("{ty_display}"),
                        doc.map(|d| d.as_str()),
                        range,
                    ));
                }

                // For Select expressions, try to find field-level docs by
                // walking the Select chain to build a field path and finding
                // the base name's type alias.
                let doc = try_select_field_doc(analysis, expr_id, docs);
                return Some(make_hover(format!("{ty_display}"), doc.as_deref(), range));
            }
        }

        node = match node.parent() {
            Some(p) => p,
            None => break,
        };
    }

    // Fallback: if the token is an attrpath key inside an attrset definition
    // (e.g. `programs.steam.enable` in `{ programs.steam.enable = true; }`),
    // resolve the type and doc from the module config type.
    try_attrpath_key_hover(analysis, &token, docs)
}

/// Hover on an attrpath key inside an attrset definition.
///
/// For `{ programs.steam.enable = true; }` in a NixOS module, hovering on
/// `steam` should show the type of `config.programs.steam` and any field-level
/// docs from the stubs.
fn try_attrpath_key_hover(
    analysis: &FileSnapshot,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
    docs: &DocIndex,
) -> Option<Hover> {
    use crate::ty_nav::{
        collect_attrpath_segments, collect_parent_attrpath_context, extract_alias_name,
        get_module_config_type, resolve_through_segments,
    };

    let inference = analysis.inference_result()?;
    let node = token.parent()?;

    // The token must be inside an Attrpath → AttrpathValue (not a Select).
    let attrpath_node = node.ancestors().find_map(rnix::ast::Attrpath::cast)?;
    let parent = attrpath_node.syntax().parent()?;
    if rnix::ast::Select::can_cast(parent.kind()) {
        return None;
    }
    let _apv = rnix::ast::AttrpathValue::cast(parent)?;

    // Find the enclosing AttrSet.
    let attrset_node = _apv.syntax().parent().and_then(rnix::ast::AttrSet::cast)?;

    // Collect all segments from this attrpath, up to and including the
    // hovered token.
    let current_segments =
        collect_attrpath_segments(&attrpath_node, token.text_range().end(), true);

    // Collect parent context from enclosing nesting.
    let parent_segments = collect_parent_attrpath_context(&attrset_node);

    // Full path = parent context + current segments.
    let mut full_path = parent_segments;
    full_path.extend(current_segments);

    if full_path.is_empty() {
        return None;
    }

    // Find the config type from the root lambda's pattern.
    let first_segment = full_path.first()?;
    let config_ty = get_module_config_type(
        analysis,
        inference,
        first_segment,
        &analysis.syntax.context_arg_types,
    )?;

    let alias = extract_alias_name(&config_ty).cloned();

    // Resolve the type at the full path.
    let resolved_ty = resolve_through_segments(&config_ty, &full_path)?;

    // Look up field doc.
    let doc = alias.as_ref().and_then(|a| {
        docs.field_doc(a.as_str(), &full_path)
            .map(|d| d.to_string())
    });

    // Show the last segment name and its type, plus any docs.
    let last_segment = full_path.last()?;
    let range = analysis.syntax.line_index.range(token.text_range());

    let type_display = format!("{last_segment} :: {resolved_ty}");

    Some(make_hover(type_display, doc.as_deref(), range))
}

/// Look up field-level docs for a token that's an attrpath key in an attrset
/// definition (e.g. `steam` in `{ programs.steam.enable = true; }`).
///
/// Builds the full path from parent context + attrpath segments, finds the
/// module config type, and queries the DocIndex for field docs at that path.
fn try_attrpath_key_field_doc(
    analysis: &FileSnapshot,
    token: &rowan::SyntaxToken<rnix::NixLanguage>,
    docs: &DocIndex,
) -> Option<String> {
    use crate::ty_nav::{
        collect_attrpath_segments, collect_parent_attrpath_context, extract_alias_name,
        get_module_config_type,
    };

    let inference = analysis.inference_result()?;
    let node = token.parent()?;

    // The token must be inside an Attrpath → AttrpathValue (not a Select).
    let attrpath_node = node.ancestors().find_map(rnix::ast::Attrpath::cast)?;
    let parent = attrpath_node.syntax().parent()?;
    if rnix::ast::Select::can_cast(parent.kind()) {
        return None;
    }
    let apv = rnix::ast::AttrpathValue::cast(parent)?;

    let attrset_node = apv.syntax().parent().and_then(rnix::ast::AttrSet::cast)?;

    let current_segments =
        collect_attrpath_segments(&attrpath_node, token.text_range().end(), true);

    let parent_segments = collect_parent_attrpath_context(&attrset_node);
    let mut full_path = parent_segments;
    full_path.extend(current_segments);

    let first_segment = full_path.first()?;
    let config_ty = get_module_config_type(
        analysis,
        inference,
        first_segment,
        &analysis.syntax.context_arg_types,
    )?;
    let alias = extract_alias_name(&config_ty)?;

    docs.field_doc(alias.as_str(), &full_path)
        .map(|d| d.to_string())
}

/// Check whether a syntax node is an attrpath element inside a Select expression.
///
/// Returns true when the node is a child of an `Attrpath` whose parent is a
/// `Select`. This correctly excludes attrpath keys in attrset definitions
/// (`AttrpathValue`) — those have a different parent type.
fn is_select_attrpath(node: &rnix::SyntaxNode) -> bool {
    node.ancestors()
        .find_map(rnix::ast::Attrpath::cast)
        .and_then(|ap| ap.syntax().parent())
        .is_some_and(|parent| rnix::ast::Select::can_cast(parent.kind()))
}

/// Walk a Select expression chain to extract the field path and look up
/// field-level docs from the DocIndex.
///
/// For `config.services.openssh.enable`, the AST is nested Selects:
///   Select(Select(Select(config, services), openssh), enable)
///
/// We walk inward to find the base name (config), then look up the
/// type alias associated with it (e.g. NixosConfig), and query the
/// DocIndex with the field path (services.openssh.enable).
fn try_select_field_doc(
    analysis: &FileSnapshot,
    expr_id: lang_ast::ExprId,
    docs: &DocIndex,
) -> Option<String> {
    use lang_ast::Literal;

    let module = &analysis.syntax.module;

    // Build the field path by walking Select chains outward.
    // The current expr_id is the outermost Select.
    let mut path = Vec::new();
    let mut current = expr_id;

    loop {
        match &module[current] {
            Expr::Select { set, attrpath, .. } => {
                // Attrpath segments are ExprIds — we need to get their string names.
                // They're typically Literal(String(...)) expressions.
                for &attr_expr in attrpath.iter().rev() {
                    if let Expr::Literal(Literal::String(s)) = &module[attr_expr] {
                        path.push(s.clone());
                    }
                }
                current = *set;
            }
            Expr::Reference(ref_name) => {
                // Found the base reference. Look up what type alias it might be.
                // Expr::Reference stores the identifier text as SmolStr.

                // Try to find the inferred type for the expression to extract
                // the alias name. If the expression type display starts with an
                // uppercase letter, it's likely a Named alias.
                let inference = analysis.inference_result()?;
                if let Some(ty) = inference.expr_ty_map.get(current) {
                    let ty_str = ty.to_string();
                    if ty_str
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_uppercase())
                    {
                        let alias_name = ty_str.split_whitespace().next().unwrap_or(&ty_str);
                        path.reverse();
                        return docs.field_doc(alias_name, &path).map(|d| d.to_string());
                    }
                }

                // Fallback: try capitalizing the base name as an alias name.
                let capitalized = capitalize_first(ref_name);
                path.reverse();
                return docs.field_doc(&capitalized, &path).map(|d| d.to_string());
            }
            _ => return None,
        }
    }
}

/// Capitalize the first character of a string.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().chain(chars).collect(),
    }
}

fn make_hover(type_text: String, doc: Option<&str>, range: Range) -> Hover {
    let mut value = format!("```tix\n{type_text}\n```");
    if let Some(doc) = doc {
        value.push_str("\n\n---\n\n");
        value.push_str(doc);
    }

    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value,
        }),
        range: Some(range),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{find_offset, parse_markers, TestAnalysis};
    use indoc::indoc;
    use lang_check::aliases::TypeAliasRegistry;

    /// Helper: hover at a byte offset and return the hover contents.
    fn hover_at(t: &TestAnalysis, offset: u32) -> Option<Hover> {
        let analysis = t.snapshot();
        let pos = analysis.syntax.line_index.position(offset);
        hover(&analysis, pos, &t.root, &t.state.registry.docs)
    }

    /// Extract the type string and optional doc string from hover contents.
    fn hover_parts(h: &Hover) -> (String, Option<String>) {
        let HoverContents::Markup(markup) = &h.contents else {
            panic!("expected Markup hover contents, got: {:?}", h.contents);
        };
        // Format is: ```tix\n<type>\n```[\n\n---\n\n<doc>]
        let value = &markup.value;
        let type_text = value
            .strip_prefix("```tix\n")
            .and_then(|s| s.split_once("\n```"))
            .map(|(ty, _)| ty.to_string())
            .unwrap_or_else(|| panic!("unexpected hover format: {value}"));
        let doc = value
            .split_once("\n```\n\n---\n\n")
            .map(|(_, doc)| doc.to_string());
        (type_text, doc)
    }

    #[test]
    fn hover_shows_decl_doc_for_global_val() {
        let stubs = r#"
            ## Build a derivation from source.
            val mkDrv :: { name: string, ... } -> { name: string, ... };
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // mkDrv is a global val — hovering on the reference should show the
        // decl doc. The expression type is the expanded function type (not
        // "mkDrv :: ...") because references show just the type.
        let src = "mkDrv { name = \"hello\"; }";
        let offset = find_offset(src, "mkDrv");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Build a derivation from source."),
            "hover on global val reference should include the stub doc comment"
        );
    }

    #[test]
    fn hover_on_name_binding_without_doc() {
        let src = indoc! {"
            let x = 1; in x
            #   ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, markers[&1]).expect("hover should return a result");
        let (type_text, doc) = hover_parts(&h);

        assert!(
            type_text.contains("int"),
            "hover should show type, got: {type_text}"
        );
        assert_eq!(doc, None, "hover should have no doc for plain let bindings");
    }

    #[test]
    fn hover_shows_field_doc_on_select() {
        let stubs = r#"
            type Config = {
                ## Whether the service is enabled.
                enable: bool,
                ...
            };
            val config :: Config;
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // Hover on the `.` to target the Select expression (not the attrpath
        // literal, which would just show `string`).
        let src = "config.enable";
        let offset = find_offset(src, ".enable");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Whether the service is enabled."),
            "hover on select should show field doc"
        );
    }

    #[test]
    fn hover_shows_nested_field_doc() {
        let stubs = r#"
            type Config = {
                services: {
                    ## SSH daemon configuration.
                    openssh: {
                        ## Whether to enable sshd.
                        enable: bool,
                        ...
                    },
                    ...
                },
                ...
            };
            val config :: Config;
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // Hover on the last `.` to get the outermost Select expression.
        let src = "config.services.openssh.enable";
        let offset = find_offset(src, ".enable");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Whether to enable sshd."),
            "hover on deeply nested select should show field doc"
        );
    }

    #[test]
    fn hover_shows_module_field_doc() {
        let stubs = r#"
            module lib {
                ## Identity function.
                val id :: a -> a;
            }
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // Use a doc comment annotation to give `lib` the type alias `Lib`.
        // Hover on the `.` to target the Select expression.
        let src = indoc! {"
            let
                /** type: lib :: Lib */
                lib = { id = x: x; };
            in lib.id
        "};
        let offset = find_offset(src, ".id");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Identity function."),
            "hover on module field should show val doc"
        );
    }

    #[test]
    fn hover_shows_docs_after_module_merge() {
        let file1 = comment_parser::parse_tix_file(
            r#"
            module lib {
                ## Identity function.
                val id :: a -> a;
            }
            "#,
        )
        .expect("parse file1");
        let file2 = comment_parser::parse_tix_file(
            r#"
            module lib {
                ## Constant function.
                val const :: a -> b -> a;
            }
            "#,
        )
        .expect("parse file2");

        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file1);
        registry.load_tix_file(&file2);

        let src = indoc! {"
            let
                /** type: lib :: Lib */
                lib = { id = x: x; const = x: y: x; };
            in lib.id
        "};
        let offset = find_offset(src, ".id");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Identity function."),
            "doc from first file should survive module merge and appear in hover"
        );
    }

    #[test]
    fn hover_shows_submodule_doc_for_flat_reexport() {
        // Flat re-exports (e.g. `lib.findFirst`) should inherit docs from
        // their submodule source (e.g. `lib.lists.findFirst`) when the flat
        // val has no doc comment of its own.
        let stubs = r#"
            module lib {
                module lists {
                    ## Find the first matching element.
                    val findFirst :: (a -> bool) -> b -> [a] -> (a | b);
                }
                val findFirst :: (a -> bool) -> b -> [a] -> (a | b);
            }
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        let src = indoc! {"
            let
                /** type: lib :: Lib */
                lib = { findFirst = x: x; };
            in lib.findFirst
        "};
        let offset = find_offset(src, ".findFirst");
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, offset).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Find the first matching element."),
            "flat re-export should inherit doc from submodule val"
        );
    }

    #[test]
    fn hover_on_attrpath_shows_field_type() {
        let stubs = r#"
            type Config = {
                ## Whether the service is enabled.
                enable: bool,
                ...
            };
            val config :: Config;
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // Hover on `enable` (the attrpath element) should show `bool`, not `string`.
        let src = indoc! {"
            config.enable
            #      ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, markers[&1]).expect("hover should return a result");
        let (type_text, _doc) = hover_parts(&h);

        assert!(
            type_text.contains("bool"),
            "hover on attrpath element should show field type `bool`, got: {type_text}"
        );
    }

    #[test]
    fn hover_on_nested_attrpath_shows_field_type() {
        // rnix parses `a.foo.bar` as a single Select with a two-element attrpath,
        // so hovering on either `foo` or `bar` walks up to the same Select node
        // and shows its result type (`int`). This is correct — previously both
        // would have shown `string` (the literal key type).
        let src = indoc! {"
            let a = { foo = { bar = 42; }; }; in a.foo.bar
            #                                        ^1 ^2
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);

        let h1 = hover_at(&t, markers[&1]).expect("hover on `foo`");
        let (ty1, _) = hover_parts(&h1);
        assert!(
            ty1.contains("int"),
            "hover on `foo` should show Select result type, got: {ty1}"
        );

        let h2 = hover_at(&t, markers[&2]).expect("hover on `bar`");
        let (ty2, _) = hover_parts(&h2);
        assert!(
            ty2.contains("int"),
            "hover on `bar` should show Select result type, got: {ty2}"
        );
    }

    #[test]
    fn hover_on_attrpath_shows_field_doc() {
        let stubs = r#"
            type Config = {
                ## Whether the service is enabled.
                enable: bool,
                ...
            };
            val config :: Config;
        "#;
        let file = comment_parser::parse_tix_file(stubs).expect("parse stubs");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // Hover on `enable` (attrpath element) should surface field docs.
        let src = indoc! {"
            config.enable
            #      ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::with_registry(src, registry);
        let h = hover_at(&t, markers[&1]).expect("hover should return a result");
        let (_type_text, doc) = hover_parts(&h);

        assert_eq!(
            doc.as_deref(),
            Some("Whether the service is enabled."),
            "hover on attrpath element should show field doc"
        );
    }

    // ==================================================================
    // Attrpath key hover (attrset definition, not Select)
    // ==================================================================

    /// Helper: set up a NixOS module context and hover at markers.
    fn hover_at_markers_with_context(
        src: &str,
        context_stubs: &str,
    ) -> std::collections::BTreeMap<u32, Option<Hover>> {
        use crate::test_util::ContextTestSetup;

        let markers = parse_markers(src);
        assert!(!markers.is_empty(), "no markers found in source");

        let ctx = ContextTestSetup::new(src, context_stubs);
        let analysis = ctx.snapshot();
        let root = ctx.root();
        let docs = ctx.docs();

        markers
            .into_iter()
            .map(|(num, offset)| {
                let pos = analysis.syntax.line_index.position(offset);
                (num, hover(&analysis, pos, &root, docs))
            })
            .collect()
    }

    #[test]
    fn hover_attrpath_key_shows_type_and_doc() {
        let stubs = indoc! {"
            type TestConfig = {
                programs: {
                    ## Whether to enable the steam game launcher.
                    steam: { enable: bool, ... },
                    firefox: { enable: bool, ... },
                    ...
                },
                ...
            };
            val config :: TestConfig;
        "};
        let src = indoc! {"
            { config, ... }: {
              programs.steam.enable = true;
            # ^1       ^2   ^3
            }
        "};
        let results = hover_at_markers_with_context(src, stubs);

        // Hover on `programs` — should show type with `:: ` format.
        let h1 = results[&1].as_ref().expect("hover on programs");
        let (ty1, _doc1) = hover_parts(h1);
        assert!(
            ty1.contains("programs"),
            "hover on `programs` attrpath key should show type, got: {ty1}"
        );
        assert!(
            ty1.contains(" :: "),
            "attrset-typed field should use `name :: type` format, got: {ty1}"
        );

        // Hover on `steam` — should show type and doc with `:: ` format.
        let h2 = results[&2].as_ref().expect("hover on steam");
        let (ty2, doc2) = hover_parts(h2);
        assert!(
            ty2.contains("steam"),
            "hover on `steam` should show type, got: {ty2}"
        );
        assert!(
            ty2.contains(" :: "),
            "attrset-typed field should use `name :: type` format, got: {ty2}"
        );
        assert_eq!(
            doc2.as_deref(),
            Some("Whether to enable the steam game launcher."),
            "hover on `steam` attrpath key should show field doc"
        );

        // Hover on `enable` — should show type (bool).
        let h3 = results[&3].as_ref().expect("hover on enable");
        let (ty3, _doc3) = hover_parts(h3);
        assert!(
            ty3.contains("bool"),
            "hover on `enable` should show bool type, got: {ty3}"
        );
    }

    #[test]
    fn hover_attrpath_key_without_destructured_config() {
        // Regression: modules that don't destructure `config` (e.g.
        // `{ pkgs, ... }:`) should still get hover info on attrpath keys
        // via the context_arg_types fallback from tix.toml.
        let stubs = indoc! {"
            type TestConfig = {
                ## System-wide packages.
                environment: {
                    ## Packages available system-wide.
                    systemPackages: [string],
                    ...
                },
                ...
            };
            type Pkgs = { hello: string, ... };
            val config :: TestConfig;
            val pkgs :: Pkgs;
        "};
        // No `config` in the pattern — only `pkgs` is destructured.
        let src = indoc! {"
            { pkgs, ... }: {
              environment.systemPackages = [];
            # ^1          ^2
            }
        "};
        let results = hover_at_markers_with_context(src, stubs);

        // Hover on `environment` — should resolve via context_arg_types fallback.
        let h1 = results[&1].as_ref().expect("hover on environment");
        let (ty1, doc1) = hover_parts(h1);
        assert!(
            ty1.contains("environment"),
            "hover on `environment` should show type, got: {ty1}"
        );
        assert_eq!(
            doc1.as_deref(),
            Some("System-wide packages."),
            "hover on `environment` should show field doc"
        );

        // Hover on `systemPackages` — nested field should also resolve.
        let h2 = results[&2].as_ref().expect("hover on systemPackages");
        let (ty2, doc2) = hover_parts(h2);
        assert!(
            ty2.contains("systemPackages"),
            "hover on `systemPackages` should show type, got: {ty2}"
        );
        assert_eq!(
            doc2.as_deref(),
            Some("Packages available system-wide."),
            "hover on `systemPackages` should show field doc"
        );
    }

    #[test]
    fn hover_attrpath_key_plain_attrset_module() {
        // Plain attrset modules (no lambda) should also get hover info
        // from context_arg_types when tix.toml provides context stubs.
        let stubs = indoc! {"
            type TestConfig = {
                ## Network configuration.
                networking: {
                    hostName: string,
                    ...
                },
                ...
            };
            val config :: TestConfig;
        "};
        let src = indoc! {"
            {
              networking.hostName = \"myhost\";
            # ^1
            }
        "};
        let results = hover_at_markers_with_context(src, stubs);

        let h1 = results[&1].as_ref().expect("hover on networking");
        let (ty1, doc1) = hover_parts(h1);
        assert!(
            ty1.contains("networking"),
            "hover on `networking` in plain attrset module should show type, got: {ty1}"
        );
        assert_eq!(
            doc1.as_deref(),
            Some("Network configuration."),
            "hover on `networking` in plain attrset module should show field doc"
        );
    }

    // ==================================================================
    // Unknown type variable display (`?` for unconstrained)
    // ==================================================================

    #[test]
    fn hover_let_binding_unconstrained_shows_question_mark() {
        // An unconstrained let binding should show `?` not a letter.
        let src = indoc! {"
            x: let y = x; in y
            #      ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, markers[&1]).expect("hover on y");
        let (type_text, _) = hover_parts(&h);

        assert!(
            type_text.contains("?"),
            "unconstrained let binding should show `?`, got: {type_text}"
        );
    }

    #[test]
    fn hover_lambda_param_unconstrained_shows_letter() {
        // A lambda param should keep a letter name even if unconstrained.
        let src = indoc! {"
            x: x
            #^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, markers[&1]).expect("hover on param x");
        let (type_text, _) = hover_parts(&h);

        assert!(
            type_text.contains("a"),
            "lambda param should keep letter name, got: {type_text}"
        );
        assert!(
            !type_text.contains("?"),
            "lambda param should not show `?`, got: {type_text}"
        );
    }

    #[test]
    fn hover_reference_to_let_binding_shows_question_mark() {
        // Hovering on a reference to an unconstrained let binding should
        // show `?` (expression path).
        let src = "x: let y = x; in y";
        let offset = find_offset(src, "in y") + 3; // position on the `y` reference
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, offset).expect("hover on reference y");
        let (type_text, _) = hover_parts(&h);

        assert!(
            type_text.contains("?"),
            "reference to unconstrained let binding should show `?`, got: {type_text}"
        );
    }

    #[test]
    fn hover_reference_to_param_shows_letter() {
        // Hovering on a reference to a lambda param should keep letters.
        let src = "x: x + 1";
        let offset = find_offset(src, ": x") + 2; // position on the `x` reference
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, offset).expect("hover on reference x");
        let (type_text, _) = hover_parts(&h);

        assert!(
            !type_text.contains("?"),
            "reference to param should show letter, got: {type_text}"
        );
    }

    #[test]
    fn hover_polymorphic_let_keeps_letters() {
        // `id = x: x` is non-param but `a` appears twice → kept as letter.
        let src = indoc! {"
            let id = x: x; in id
            #   ^1
        "};
        let markers = parse_markers(src);
        let t = TestAnalysis::new(src);
        let h = hover_at(&t, markers[&1]).expect("hover on id");
        let (type_text, _) = hover_parts(&h);

        assert!(
            type_text.contains("a -> a"),
            "polymorphic let binding should keep letters, got: {type_text}"
        );
        assert!(
            !type_text.contains("?"),
            "polymorphic let binding should not show `?`, got: {type_text}"
        );
    }
}
