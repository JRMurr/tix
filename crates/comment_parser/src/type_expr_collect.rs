// =============================================================================
// Shared type-expression collection (Rule-parameterized)
// =============================================================================
//
// pest generates a separate, incompatible `Rule` enum per parser, so the
// type-expression collection functions cannot be ordinary generic functions.
// Both grammars now share `type_expr.pest`, which guarantees the rule
// *variant names* are identical — this macro stamps out one copy of the
// collection suite per parser module, resolving `Rule::...` against whatever
// `Rule` is in scope at the expansion site.
//
// Invoked by `collect.rs` (doc comment parser) and `tix_collect.rs`
// (.tix file parser). Field doc / @source accumulation is threaded through
// `CollectCtx` in both; the doc comment entry point simply discards it.

/// Emit the type-expression collection functions for the `Rule` enum in scope.
macro_rules! impl_type_expr_collection {
    () => {
        /// Extract the joined text of a `doc_block` (one or more `##` lines),
        /// stripping the `## ` prefix from each line.
        fn extract_doc_block(pair: &pest::iterators::Pair<Rule>) -> SmolStr {
            debug_assert_eq!(pair.as_rule(), Rule::doc_block);
            let lines: Vec<&str> = pair
                .clone()
                .into_inner()
                .map(|comment| {
                    let text = comment.as_str();
                    // Strip the `##` prefix.
                    let rest = &text[2..];
                    // Strip a single leading space if present (conventional `## text`).
                    rest.strip_prefix(' ').unwrap_or(rest)
                })
                .collect();
            SmolStr::from(lines.join("\n"))
        }

        /// Consume a leading `doc_block` child, if present.
        fn take_doc_block(inner: &mut Pairs<Rule>) -> Option<SmolStr> {
            let first = inner.peek()?;
            if first.as_rule() == Rule::doc_block {
                let doc = extract_doc_block(&first);
                inner.next(); // consume it
                Some(doc)
            } else {
                None
            }
        }

        /// Consume a leading `source_annotation` child, if present.
        fn take_source_annotation(inner: &mut Pairs<Rule>) -> Option<$crate::SourceLocation> {
            let first = inner.peek()?;
            if first.as_rule() == Rule::source_annotation {
                inner.next(); // consume the source_annotation pair
                let source_loc = first.into_inner().next()?; // the source_loc child
                $crate::collect_shared::parse_source_loc(source_loc.as_str().trim())
            } else {
                None
            }
        }

        /// Helper to build a CollectError with span information from a pest Pair.
        fn err_at_pair(
            message: impl Into<String>,
            pair: &pest::iterators::Pair<Rule>,
        ) -> CollectError {
            let span = pair.as_span();
            CollectError::with_span(message, span.start(), span.end())
        }

        fn collect_type_expr(
            mut pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<Option<ParsedTy>, CollectError> {
            let curr = match pairs.next() {
                Some(c) => c,
                None => return Ok(None),
            };

            let curr = match curr.as_rule() {
                // Transparent wrappers — descend into their single child.
                Rule::type_expr
                | Rule::arrow_segment
                | Rule::paren_type
                | Rule::type_ref
                | Rule::primitive_ref
                | Rule::atom_type => {
                    collect_type_expr(curr.into_inner(), ctx)?.ok_or_else(|| {
                        CollectError::new("expected type expression inside wrapper, found empty")
                    })?
                }

                Rule::union_type => collect_union(curr.into_inner(), ctx)?,
                Rule::isect_type => collect_intersection(curr.into_inner(), ctx)?,
                Rule::postfix_type => collect_postfix(curr.into_inner(), ctx)?,
                Rule::typeof_expr => collect_typeof(curr.into_inner())?,
                Rule::import_type => collect_import_type(curr.into_inner())?,
                Rule::applied_type => collect_applied_type(curr.into_inner(), ctx)?,

                Rule::attrset_type => collect_attrset(curr.into_inner(), ctx)?,
                Rule::list_type => {
                    let inner = collect_type_expr(curr.into_inner(), ctx)?
                        .ok_or_else(|| CollectError::new("list type has empty element type"))?;
                    ParsedTy::List(inner.into())
                }
                Rule::string_ref => ParsedTy::Primitive(PrimitiveTy::String),
                Rule::number_ref => ParsedTy::Primitive(PrimitiveTy::Number),
                Rule::int_ref => ParsedTy::Primitive(PrimitiveTy::Int),
                Rule::bool_ref => ParsedTy::Primitive(PrimitiveTy::Bool),
                Rule::float_ref => ParsedTy::Primitive(PrimitiveTy::Float),
                Rule::path_ref => ParsedTy::Primitive(PrimitiveTy::Path),
                Rule::null_ref => ParsedTy::Primitive(PrimitiveTy::Null),
                Rule::any_ref => ParsedTy::Top,
                Rule::never_ref => ParsedTy::Bottom,
                Rule::generic_ident => ParsedTy::TyVar(TypeVarValue::Generic(curr.as_str().into())),
                Rule::user_type => ParsedTy::TyVar(TypeVarValue::Reference(curr.as_str().into())),
                // EOI can appear as a trailing child (e.g. a doc comment
                // annotation ending without a newline). Not a type expression.
                Rule::EOI => return Ok(None),
                _ => {
                    return Err(err_at_pair(
                        format!("unexpected rule {:?} in type expression", curr.as_rule()),
                        &curr,
                    ));
                }
            };

            // Arrow chaining: right-associative lambdas.
            if let Some(lam_body) = collect_type_expr(pairs, ctx)? {
                return Ok(Some(ParsedTy::Lambda {
                    param: curr.into(),
                    body: lam_body.into(),
                }));
            }

            Ok(Some(curr))
        }

        /// Collect a single type from a Pair. Unlike `collect_type_expr`, this
        /// does NOT treat remaining items as lambda body — it processes exactly
        /// one rule node.
        fn collect_one(
            pair: pest::iterators::Pair<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            match pair.as_rule() {
                Rule::isect_type => collect_intersection(pair.into_inner(), ctx),
                Rule::postfix_type => collect_postfix(pair.into_inner(), ctx),
                Rule::typeof_expr => collect_typeof(pair.into_inner()),
                Rule::import_type => collect_import_type(pair.into_inner()),
                Rule::applied_type => collect_applied_type(pair.into_inner(), ctx),
                Rule::atom_type
                | Rule::paren_type
                | Rule::type_ref
                | Rule::primitive_ref
                | Rule::arrow_segment
                | Rule::union_type
                | Rule::type_expr => collect_type_expr(pair.into_inner(), ctx)?
                    .ok_or_else(|| CollectError::new("expected type expression, found empty")),
                Rule::attrset_type => collect_attrset(pair.into_inner(), ctx),
                Rule::list_type => {
                    let inner = collect_type_expr(pair.into_inner(), ctx)?
                        .ok_or_else(|| CollectError::new("list type has empty element type"))?;
                    Ok(ParsedTy::List(inner.into()))
                }
                Rule::string_ref => Ok(ParsedTy::Primitive(PrimitiveTy::String)),
                Rule::number_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Number)),
                Rule::int_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Int)),
                Rule::bool_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Bool)),
                Rule::float_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Float)),
                Rule::path_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Path)),
                Rule::null_ref => Ok(ParsedTy::Primitive(PrimitiveTy::Null)),
                Rule::any_ref => Ok(ParsedTy::Top),
                Rule::never_ref => Ok(ParsedTy::Bottom),
                Rule::generic_ident => {
                    Ok(ParsedTy::TyVar(TypeVarValue::Generic(pair.as_str().into())))
                }
                Rule::user_type => Ok(ParsedTy::TyVar(TypeVarValue::Reference(
                    pair.as_str().into(),
                ))),
                _ => Err(err_at_pair(
                    format!("unexpected rule {:?} in type expression", pair.as_rule()),
                    &pair,
                )),
            }
        }

        /// Collect a postfix field access chain: `atom_type ("." field_access_key)*`.
        /// Wraps the base type in FieldAccess for each `.key` suffix.
        fn collect_postfix(
            pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            let mut iter = pairs;
            let base_pair = iter
                .next()
                .ok_or_else(|| CollectError::new("postfix_type missing base type"))?;
            let mut result = collect_one(base_pair, ctx)?;
            for key_pair in iter {
                if key_pair.as_rule() == Rule::field_access_key {
                    result = ParsedTy::FieldAccess(
                        ParsedTyRef::from(result),
                        SmolStr::from(key_pair.as_str()),
                    );
                }
            }
            Ok(result)
        }

        /// Collect a typeof expression: `typeof_kw (import_path | identifier)`.
        fn collect_typeof(pairs: Pairs<Rule>) -> Result<ParsedTy, CollectError> {
            let mut iter = pairs;
            // Skip typeof_kw
            let _kw = iter
                .next()
                .ok_or_else(|| CollectError::new("typeof_expr missing keyword"))?;
            let target = iter
                .next()
                .ok_or_else(|| CollectError::new("typeof_expr missing target"))?;
            match target.as_rule() {
                Rule::import_path => {
                    let path = extract_import_path(target)?;
                    Ok(ParsedTy::TypeOfImport(path))
                }
                Rule::identifier => Ok(ParsedTy::TypeOf(SmolStr::from(target.as_str()))),
                _ => Err(err_at_pair(
                    format!("unexpected rule {:?} in typeof_expr", target.as_rule()),
                    &target,
                )),
            }
        }

        /// Collect a cross-file type import: `import_kw "(" string_literal ")" "." user_type`.
        fn collect_import_type(pairs: Pairs<Rule>) -> Result<ParsedTy, CollectError> {
            let mut iter = pairs;
            // Skip import_kw
            let _kw = iter
                .next()
                .ok_or_else(|| CollectError::new("import_type missing keyword"))?;
            let path_pair = iter
                .next()
                .ok_or_else(|| CollectError::new("import_type missing path"))?;
            let path = $crate::collect_shared::unquote_string_literal(path_pair.as_str());
            let type_name = iter
                .next()
                .ok_or_else(|| CollectError::new("import_type missing type name"))?;
            Ok(ParsedTy::ImportType(
                path,
                SmolStr::from(type_name.as_str()),
            ))
        }

        /// Collect an applied type: `type_func "(" type_expr ")"`.
        fn collect_applied_type(
            pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            let mut iter = pairs;
            let func = iter
                .next()
                .ok_or_else(|| CollectError::new("applied_type missing function"))?;
            let func_name = func.as_str();
            let inner = collect_type_expr(iter, ctx)?
                .ok_or_else(|| CollectError::new("applied_type missing inner type"))?;
            match func_name {
                "Param" => Ok(ParsedTy::Param(ParsedTyRef::from(inner))),
                "Return" => Ok(ParsedTy::Return(ParsedTyRef::from(inner))),
                _ => Err(CollectError::new(format!(
                    "unknown type function: {func_name}"
                ))),
            }
        }

        /// Extract the path string from an import_path rule.
        fn extract_import_path(pair: pest::iterators::Pair<Rule>) -> Result<String, CollectError> {
            let mut iter = pair.into_inner();
            // Skip import_kw
            let _kw = iter
                .next()
                .ok_or_else(|| CollectError::new("import_path missing keyword"))?;
            let path_pair = iter
                .next()
                .ok_or_else(|| CollectError::new("import_path missing path"))?;
            Ok($crate::collect_shared::unquote_string_literal(
                path_pair.as_str(),
            ))
        }

        /// Collect a union type: `isect_type ("|" isect_type)*`.
        /// If only one member, returns it directly (no spurious Union wrapper).
        fn collect_union(
            pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            let members: Result<Vec<ParsedTyRef>, CollectError> = pairs
                .map(|p| collect_one(p, ctx).map(ParsedTyRef::from))
                .collect();
            $crate::collect_shared::normalize_set_type(members?, "union", ParsedTy::Union)
        }

        /// Collect an intersection type: `postfix_type ("&" postfix_type)*`.
        fn collect_intersection(
            pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            let members: Result<Vec<ParsedTyRef>, CollectError> = pairs
                .map(|p| collect_one(p, ctx).map(ParsedTyRef::from))
                .collect();
            $crate::collect_shared::normalize_set_type(
                members?,
                "intersection",
                ParsedTy::Intersection,
            )
        }

        /// Collect an attrset type: `named_field*`, optional `dyn_field`,
        /// optional `open_marker`. Field-level doc comments and @source
        /// annotations are pushed into `ctx` with the current nesting path.
        fn collect_attrset(
            pairs: Pairs<Rule>,
            ctx: &mut $crate::collect_shared::CollectCtx,
        ) -> Result<ParsedTy, CollectError> {
            let mut fields: std::collections::BTreeMap<SmolStr, ParsedTyRef> =
                std::collections::BTreeMap::new();
            let mut dyn_ty: Option<ParsedTyRef> = None;
            let mut open = false;
            let mut optional_fields = std::collections::BTreeSet::new();

            let parent_path = ctx.path().to_vec();

            for pair in pairs {
                match pair.as_rule() {
                    Rule::named_field => {
                        let mut inner = pair.into_inner();
                        // Check for a doc_block on the field.
                        let field_doc = take_doc_block(&mut inner);

                        let field_source = take_source_annotation(&mut inner);

                        let name_pair = inner
                            .next()
                            .ok_or_else(|| CollectError::new("named_field missing field name"))?;
                        // quoted_field includes surrounding quotes -- strip them.
                        let name: SmolStr = match name_pair.as_rule() {
                            Rule::quoted_field => {
                                let raw = name_pair.as_str();
                                raw[1..raw.len() - 1].into()
                            }
                            _ => name_pair.as_str().into(),
                        };

                        // Check for optional_marker (`?` after the field name).
                        if inner
                            .peek()
                            .is_some_and(|p| p.as_rule() == Rule::optional_marker)
                        {
                            inner.next(); // consume the `?`
                            optional_fields.insert(name.clone());
                        }

                        // If this field has a doc comment or @source, record them.
                        if let Some(doc) = field_doc {
                            ctx.push_field_doc(name.clone(), doc);
                        }
                        if let Some(source) = field_source {
                            ctx.push_field_source(name.clone(), source);
                        }

                        // Set path context for nested attrsets so their field docs
                        // and @source annotations get the correct prefix.
                        let mut child_path = parent_path.clone();
                        child_path.push(name.clone());
                        ctx.set_path(child_path);

                        let ty = collect_type_expr(inner, ctx)?.ok_or_else(|| {
                            CollectError::new(format!("field '{name}' has empty type"))
                        })?;
                        fields.insert(name, ty.into());

                        // Restore parent path context.
                        ctx.set_path(parent_path.clone());
                    }
                    Rule::dyn_field => {
                        let inner = pair.into_inner();
                        let ty = collect_type_expr(inner, ctx)?
                            .ok_or_else(|| CollectError::new("dynamic field has empty type"))?;
                        dyn_ty = Some(ty.into());
                    }
                    Rule::open_marker => {
                        open = true;
                    }
                    _ => {
                        return Err(err_at_pair(
                            format!("unexpected rule {:?} in attrset type", pair.as_rule()),
                            &pair,
                        ));
                    }
                }
            }

            Ok(ParsedTy::AttrSet(lang_ty::AttrSetTy {
                fields,
                dyn_ty,
                open,
                optional_fields,
            }))
        }
    };
}

pub(crate) use impl_type_expr_collection;
