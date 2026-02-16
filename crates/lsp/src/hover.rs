// ==============================================================================
// textDocument/hover — show inferred type on hover
// ==============================================================================
//
// Converts the cursor position to a byte offset, finds the smallest syntax
// node at that offset, maps it to an ExprId or NameId via the source map,
// then looks up the inferred type. If stub docs are available for the hovered
// name or field, they're appended below the type.

use lang_ast::{AstPtr, Expr};
use lang_check::aliases::DocIndex;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{Hover, HoverContents, MarkedString, Position, Range};

use crate::state::FileAnalysis;

/// Try to produce hover information for the given cursor position.
pub fn hover(
    analysis: &FileAnalysis,
    pos: Position,
    root: &rnix::Root,
    docs: &DocIndex,
) -> Option<Hover> {
    let inference = analysis.inference()?;
    let offset = analysis.line_index.offset(pos);
    let token = root
        .syntax()
        .token_at_offset(rowan::TextSize::from(offset))
        .right_biased()?;

    // Walk up from the token to find the smallest node that has a source map entry.
    let mut node = token.parent()?;
    loop {
        let ptr = AstPtr::new(&node);

        // Check for a name at this node first (shows the binding's type).
        if let Some(name_id) = analysis.source_map.name_for_node(ptr) {
            if let Some(ty) = inference.name_ty_map.get(name_id) {
                let name_text = &analysis.module[name_id].text;
                let range = analysis.line_index.range(node.text_range());

                // Look up doc comment for this name from stubs.
                let doc = docs.decl_doc(name_text.as_str());
                return Some(make_hover(
                    format!("{name_text} :: {ty}"),
                    doc.map(|d| d.as_str()),
                    range,
                ));
            }
        }

        // Then check for an expression.
        if let Some(expr_id) = analysis.source_map.expr_for_node(ptr) {
            if let Some(ty) = inference.expr_ty_map.get(expr_id) {
                let range = analysis.line_index.range(node.text_range());

                // For Reference expressions (variable uses), look up decl_doc
                // by the referenced name. This surfaces docs for global vals
                // from stubs (e.g. hovering on `mkDerivation` shows its doc).
                if let Expr::Reference(ref_name) = &analysis.module[expr_id] {
                    let doc = docs.decl_doc(ref_name.as_str());
                    return Some(make_hover(
                        format!("{ty}"),
                        doc.map(|d| d.as_str()),
                        range,
                    ));
                }

                // For Select expressions, try to find field-level docs by
                // walking the Select chain to build a field path and finding
                // the base name's type alias.
                let doc = try_select_field_doc(analysis, expr_id, docs);
                return Some(make_hover(format!("{ty}"), doc.as_deref(), range));
            }
        }

        node = node.parent()?;
    }
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
    analysis: &FileAnalysis,
    expr_id: lang_ast::ExprId,
    docs: &DocIndex,
) -> Option<String> {
    use lang_ast::Literal;

    let module = &analysis.module;

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
                let inference = analysis.inference()?;
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
    let mut parts = vec![MarkedString::LanguageString(
        tower_lsp::lsp_types::LanguageString {
            language: "tix".to_string(),
            value: type_text,
        },
    )];

    if let Some(doc) = doc {
        parts.push(MarkedString::String(doc.to_string()));
    }

    Hover {
        contents: HoverContents::Array(parts),
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
        let analysis = t.analysis();
        let pos = analysis.line_index.position(offset);
        hover(analysis, pos, &t.root, &t.state.registry.docs)
    }

    /// Extract the type string and optional doc string from hover contents.
    fn hover_parts(h: &Hover) -> (String, Option<String>) {
        let HoverContents::Array(parts) = &h.contents else {
            panic!("expected Array hover contents");
        };
        let type_text = match &parts[0] {
            MarkedString::LanguageString(ls) => ls.value.clone(),
            other => panic!("expected LanguageString, got: {other:?}"),
        };
        let doc = parts.get(1).map(|p| match p {
            MarkedString::String(s) => s.clone(),
            other => panic!("expected String for doc, got: {other:?}"),
        });
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
}
