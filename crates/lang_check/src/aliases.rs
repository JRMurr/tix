// ==============================================================================
// Type Alias Registry
// ==============================================================================
//
// Holds type aliases and global val declarations loaded from .tix stub files.
// `TypeAliasRegistry` is built before inference begins and passed into `CheckCtx`
// so that `TypeVarValue::Reference` names resolve against loaded aliases, and
// unresolved names can fall back to global val declarations.

use std::collections::HashMap;

use comment_parser::{ParsedTy, ParsedTyRef, TixDeclFile, TixDeclaration};
use lang_ty::AttrSetTy;
use smol_str::SmolStr;

#[derive(Debug, Clone, Default)]
pub struct TypeAliasRegistry {
    /// Type alias name -> body (e.g. `Derivation` -> `{ name: string, ... }`)
    aliases: HashMap<SmolStr, ParsedTy>,

    /// Top-level val declarations (e.g. `mkDerivation` -> `{ name: string, ... } -> Derivation`)
    global_vals: HashMap<SmolStr, ParsedTy>,
}

impl TypeAliasRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Load declarations from a parsed .tix file into the registry.
    pub fn load_tix_file(&mut self, file: &TixDeclFile) {
        self.load_declarations(&file.declarations, true);
    }

    /// Recursively load declarations. `top_level` controls whether val
    /// declarations are added to `global_vals` (only at the top level).
    fn load_declarations(&mut self, declarations: &[TixDeclaration], top_level: bool) {
        for decl in declarations {
            match decl {
                TixDeclaration::TypeAlias { name, body } => {
                    self.aliases.insert(name.clone(), body.clone());
                }
                TixDeclaration::ValDecl { name, ty } => {
                    if top_level {
                        self.global_vals.insert(name.clone(), ty.clone());
                    }
                }
                TixDeclaration::Module { name, declarations } => {
                    // Convert the module into an attrset type and register it
                    // as a type alias with the capitalized module name.
                    // e.g. `module lib { val id :: a -> a; }` -> alias "Lib" = { id: a -> a, ... }
                    let attrset_ty = module_to_attrset(declarations);
                    let alias_name = capitalize(name);
                    self.aliases.insert(alias_name, attrset_ty);
                }
            }
        }
    }

    /// Look up a type alias by name.
    pub fn get(&self, name: &str) -> Option<&ParsedTy> {
        self.aliases.get(name)
    }

    /// Get the global val declarations map.
    pub fn global_vals(&self) -> &HashMap<SmolStr, ParsedTy> {
        &self.global_vals
    }

    /// Validate the registry for cycles in alias references.
    /// Returns `Err` with the names involved in cycles if any are found.
    pub fn validate(&self) -> Result<(), Vec<SmolStr>> {
        let mut cycles = Vec::new();
        let mut visited = HashMap::<SmolStr, VisitState>::new();

        for name in self.aliases.keys() {
            if self.has_cycle(name, &mut visited) {
                cycles.push(name.clone());
            }
        }

        if cycles.is_empty() {
            Ok(())
        } else {
            Err(cycles)
        }
    }

    /// DFS cycle detection for alias references.
    fn has_cycle(&self, name: &SmolStr, visited: &mut HashMap<SmolStr, VisitState>) -> bool {
        match visited.get(name) {
            Some(VisitState::InProgress) => return true,
            Some(VisitState::Done) => return false,
            None => {}
        }

        visited.insert(name.clone(), VisitState::InProgress);

        if let Some(body) = self.aliases.get(name) {
            let refs = collect_references(body);
            for ref_name in refs {
                if self.aliases.contains_key(ref_name.as_str())
                    && self.has_cycle(&ref_name, visited)
                {
                    return true;
                }
            }
        }

        visited.insert(name.clone(), VisitState::Done);
        false
    }
}

#[derive(Debug, Clone, Copy)]
enum VisitState {
    InProgress,
    Done,
}

/// Capitalize the first character of a string (e.g. "lib" -> "Lib").
fn capitalize(s: &str) -> SmolStr {
    let mut chars = s.chars();
    match chars.next() {
        None => SmolStr::default(),
        Some(first) => {
            let capitalized: String = first.to_uppercase().chain(chars).collect();
            SmolStr::from(capitalized)
        }
    }
}

/// Convert a module's declarations into an open attrset ParsedTy.
/// Val declarations become named fields; nested modules become nested attrset fields.
fn module_to_attrset(declarations: &[TixDeclaration]) -> ParsedTy {
    let mut fields = std::collections::BTreeMap::new();

    for decl in declarations {
        match decl {
            TixDeclaration::ValDecl { name, ty } => {
                fields.insert(name.clone(), ParsedTyRef::from(ty.clone()));
            }
            TixDeclaration::Module {
                name,
                declarations: nested,
            } => {
                let nested_attrset = module_to_attrset(nested);
                fields.insert(name.clone(), ParsedTyRef::from(nested_attrset));
            }
            // Type aliases inside modules define types but don't add attrset fields.
            TixDeclaration::TypeAlias { .. } => {}
        }
    }

    ParsedTy::AttrSet(AttrSetTy {
        fields,
        dyn_ty: None,
        open: true,
    })
}

/// Collect all `TypeVarValue::Reference` names from a ParsedTy.
fn collect_references(ty: &ParsedTy) -> Vec<SmolStr> {
    let mut refs = Vec::new();
    collect_references_inner(ty, &mut refs);
    refs
}

fn collect_references_inner(ty: &ParsedTy, refs: &mut Vec<SmolStr>) {
    match ty {
        ParsedTy::TyVar(comment_parser::TypeVarValue::Reference(name)) => {
            refs.push(name.clone());
        }
        ParsedTy::TyVar(comment_parser::TypeVarValue::Generic(_)) => {}
        ParsedTy::Primitive(_) => {}
        ParsedTy::List(inner) => collect_references_inner(&inner.0, refs),
        ParsedTy::Lambda { param, body } => {
            collect_references_inner(&param.0, refs);
            collect_references_inner(&body.0, refs);
        }
        ParsedTy::AttrSet(attr) => {
            for v in attr.fields.values() {
                collect_references_inner(&v.0, refs);
            }
            if let Some(dyn_ty) = &attr.dyn_ty {
                collect_references_inner(&dyn_ty.0, refs);
            }
        }
        ParsedTy::Union(members) | ParsedTy::Intersection(members) => {
            for m in members {
                collect_references_inner(&m.0, refs);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use comment_parser::parse_tix_file;

    #[test]
    fn load_type_alias() {
        let file = parse_tix_file("type Derivation = { name: string };").expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.get("Derivation").is_some());
        assert!(registry.validate().is_ok());
    }

    #[test]
    fn load_val_decl() {
        let file = parse_tix_file("val mkDerivation :: { name: string, ... } -> { name: string };")
            .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.global_vals().get("mkDerivation").is_some());
    }

    #[test]
    fn module_becomes_alias() {
        let file = parse_tix_file(
            r#"
            module lib {
                val id :: a -> a;
                module strings {
                    val concatStringsSep :: string -> [string] -> string;
                }
            }
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        // "Lib" alias should exist (capitalized from "lib")
        let lib_ty = registry.get("Lib").expect("Lib alias should exist");
        match lib_ty {
            ParsedTy::AttrSet(attr) => {
                assert!(attr.fields.contains_key("id"));
                assert!(attr.fields.contains_key("strings"));
                assert!(attr.open);
            }
            other => panic!("expected AttrSet, got: {other:?}"),
        }
    }

    #[test]
    fn cycle_detection() {
        let file = parse_tix_file(
            r#"
            type A = B;
            type B = A;
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.validate().is_err());
    }

    #[test]
    fn no_false_cycle() {
        let file = parse_tix_file(
            r#"
            type Derivation = { name: string };
            type Nullable = a | null;
            "#,
        )
        .expect("parse error");
        let mut registry = TypeAliasRegistry::new();
        registry.load_tix_file(&file);

        assert!(registry.validate().is_ok());
    }
}
