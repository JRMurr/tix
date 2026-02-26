// ==============================================================================
// textDocument/documentLink — clickable import paths
// ==============================================================================
//
// Leverages the existing import_targets map to produce clickable links for
// `import ./path.nix` expressions.

use lang_ast::Expr;
use rowan::ast::AstNode;
use tower_lsp::lsp_types::{DocumentLink, Url};

use crate::state::FileSnapshot;

pub fn document_links(analysis: &FileSnapshot, root: &rnix::Root) -> Vec<DocumentLink> {
    let mut links = Vec::new();

    for (&expr_id, target_path) in &analysis.syntax.import_targets {
        // We want the range of the path literal specifically, not the whole
        // Apply expression. Walk the expression to find the innermost path
        // or string literal that represents the import target.
        let range = match &analysis.syntax.module[expr_id] {
            Expr::Literal(lang_ast::Literal::Path(_)) => {
                // This expr IS the path literal — use its range directly.
                analysis.syntax.source_map.node_for_expr(expr_id).map(|ptr| {
                    let node = ptr.to_node(root.syntax());
                    analysis.syntax.line_index.range(node.text_range())
                })
            }
            // For Apply expressions (e.g. `import ./foo.nix`), the import_targets
            // map also includes the Apply node itself. We only want the path literal,
            // so skip non-literal entries.
            _ => continue,
        };

        let range = match range {
            Some(r) => r,
            None => continue,
        };

        let target = match Url::from_file_path(target_path) {
            Ok(u) => u,
            Err(_) => continue,
        };

        links.push(DocumentLink {
            range,
            target: Some(target),
            tooltip: Some(format!("{}", target_path.display())),
            data: None,
        });
    }

    links
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::AnalysisState;
    use crate::test_util::{temp_path, TempProject};
    use lang_check::aliases::TypeAliasRegistry;

    #[test]
    fn import_produces_link() {
        let project = TempProject::new(&[("main.nix", "import ./lib.nix"), ("lib.nix", "42")]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let contents = std::fs::read_to_string(&main_path).unwrap();
        state.update_file(main_path.clone(), contents.clone());
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let links = document_links(&analysis, &root);
        assert!(!links.is_empty(), "should produce at least one link");

        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        let has_lib_link = links.iter().any(|l| l.target.as_ref() == Some(&lib_uri));
        assert!(has_lib_link, "should have a link to lib.nix");
    }

    #[test]
    fn let_import_produces_link() {
        let project = TempProject::new(&[
            ("main.nix", "let lib = import ./lib.nix; in lib"),
            ("lib.nix", "42"),
        ]);
        let main_path = project.path("main.nix");
        let lib_path = project.path("lib.nix");

        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        let contents = std::fs::read_to_string(&main_path).unwrap();
        state.update_file(main_path.clone(), contents.clone());
        let analysis = state.get_file(&main_path).unwrap().to_snapshot();
        let root = rnix::Root::parse(&contents).tree();

        let links = document_links(&analysis, &root);
        let lib_uri = Url::from_file_path(&lib_path).unwrap();
        let has_lib_link = links.iter().any(|l| l.target.as_ref() == Some(&lib_uri));
        assert!(has_lib_link, "should have a link to lib.nix");
    }

    #[test]
    fn no_links_for_plain_expression() {
        let path = temp_path("test.nix");
        let mut state = AnalysisState::new(TypeAliasRegistry::default());
        state.update_file(path.clone(), "42".to_string());
        let analysis = state.get_file(&path).unwrap().to_snapshot();
        let root = rnix::Root::parse("42").tree();

        let links = document_links(&analysis, &root);
        assert!(links.is_empty());
    }
}
