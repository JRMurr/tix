use std::collections::HashMap;

use id_arena::Arena;
use rnix::ast::{self, HasEntry};

use rowan::ast::AstNode;

use crate::lang::Pat;

use super::{
    AstPtr, Attrpath, BindingValue, Bindings, Expr, ExprId, InterpolPart, Literal, Module,
    ModuleSourceMap, Name, NameId,
    ast_utils::{AttrKind, get_str_literal, name_of_ident},
};

struct LowerCtx {
    // TODO: might want a mapping here of exprs/bindings to their doc/type comments
    // can get later with the source map but might be slower?
    exprs: Arena<Expr>,
    names: Arena<Name>,
    source_map: ModuleSourceMap,
}

#[allow(dead_code)]
pub fn lower(root: rnix::Root) -> (Module, ModuleSourceMap) {
    let mut ctx = LowerCtx {
        exprs: Arena::new(),
        names: Arena::new(),
        source_map: ModuleSourceMap::default(),
    };

    let entry = ctx.lower_expr_opt(root.expr());
    let module = Module {
        exprs: ctx.exprs,
        names: ctx.names,
        entry_expr: entry,
    };
    (module, ctx.source_map)
}

impl LowerCtx {
    fn alloc_expr(&mut self, expr: Expr, ptr: AstPtr) -> ExprId {
        let id = self.exprs.alloc(expr);
        self.source_map.insert_expr(id, ptr);
        id
    }

    fn alloc_name(&mut self, text: String, ptr: AstPtr) -> NameId {
        let id = self.names.alloc(text);
        self.source_map.insert_name(id, ptr);
        id
    }

    fn lower_expr_opt(&mut self, expr: Option<ast::Expr>) -> ExprId {
        if let Some(expr) = expr {
            return self.lower_expr(expr);
        }
        // Synthetic syntax has no corresponding text.
        self.exprs.alloc(Expr::Missing)
    }

    fn lower_expr(&mut self, rnix_expr: ast::Expr) -> ExprId {
        let ptr = AstPtr::new(rnix_expr.syntax());

        let expr: Expr = match rnix_expr {
            ast::Expr::Apply(apply) => {
                let fun = self.lower_expr_opt(apply.lambda());
                let arg = self.lower_expr_opt(apply.argument());
                Expr::Apply { fun, arg }
            }
            ast::Expr::IfElse(if_else) => {
                let cond = self.lower_expr_opt(if_else.condition());
                let then_body = self.lower_expr_opt(if_else.body());
                let else_body = self.lower_expr_opt(if_else.else_body());

                Expr::IfThenElse {
                    cond,
                    then_body,
                    else_body,
                }
            }
            ast::Expr::Select(select) => {
                let set = self.lower_expr_opt(select.expr());
                let attrpath = self.lower_attrpath_opt(select.attrpath());
                let default_expr = select.default_expr().map(|e| self.lower_expr(e));

                Expr::Select {
                    set,
                    attrpath,
                    default_expr,
                }
            }
            ast::Expr::With(with) => {
                let env = self.lower_expr_opt(with.namespace());
                let body = self.lower_expr_opt(with.body());
                Expr::With { env, body }
            }
            ast::Expr::HasAttr(has_attr) => {
                let set = self.lower_expr_opt(has_attr.expr());
                let attrpath = self.lower_attrpath_opt(has_attr.attrpath());

                Expr::HasAttr { set, attrpath }
            }
            ast::Expr::Str(s) => return self.lower_string(s),
            ast::Expr::Path(_path) => {
                // TODO: real handling
                Expr::Literal(Literal::Path("TODO!".to_string()))
            }
            ast::Expr::Literal(literal) => {
                // TODO: no expect...., should do missing if its sad..
                let lit = match literal.kind() {
                    ast::LiteralKind::Float(float) => {
                        let val = float.value().expect("should be valid float");
                        Literal::Float(ordered_float::OrderedFloat(val))
                    }
                    ast::LiteralKind::Integer(integer) => {
                        Literal::Integer(integer.value().expect("should be valid integer"))
                    }
                    ast::LiteralKind::Uri(_uri) => Literal::Uri,
                };

                Expr::Literal(lit)
            }
            ast::Expr::Lambda(lambda) => return self.lower_lambda(lambda, ptr),
            ast::Expr::LetIn(let_in) => {
                let bindings = MergingSet::desugar(self, &let_in).finish(self);
                let body = self.lower_expr_opt(let_in.body());
                Expr::LetIn { bindings, body }
            }
            ast::Expr::List(list) => {
                let elems = list.items().map(|elem| self.lower_expr(elem));

                Expr::List(elems.collect())
            }
            ast::Expr::BinOp(bin_op) => {
                let lhs = self.lower_expr_opt(bin_op.lhs());

                // TODO: handle this better, maybe keep the option in the expr type?
                let op = bin_op.operator().expect("Should have operator");

                let rhs = self.lower_expr_opt(bin_op.rhs());

                Expr::BinOp { lhs, rhs, op }
            }
            ast::Expr::Paren(paren) => return self.lower_expr_opt(paren.expr()),
            ast::Expr::AttrSet(attr_set) => {
                let bindings = MergingSet::desugar(self, &attr_set).finish(self);

                Expr::AttrSet {
                    is_rec: attr_set.rec_token().is_some(),
                    bindings,
                }
            }
            ast::Expr::UnaryOp(unary_op) => {
                let op = unary_op.operator().expect("Should have operator");

                let expr = self.lower_expr_opt(unary_op.expr());

                Expr::UnaryOp { op, expr }
            }
            ast::Expr::Ident(ident) => {
                Expr::Reference(name_of_ident(&ident).expect("Should have name"))
            }
            ast::Expr::Assert(assert) => {
                let cond = self.lower_expr_opt(assert.condition());
                let body = self.lower_expr_opt(assert.body());

                Expr::Assert { cond, body }
            }
            ast::Expr::Error(error) => {
                eprintln!("!!!!!!!!Hit error node {}", error.syntax());
                Expr::Missing
            }
            ast::Expr::Root(root) => {
                eprintln!("Handling root");
                return self.lower_expr_opt(root.expr());
            }
            ast::Expr::LegacyLet(_legacy_let) => todo!(),
        };

        self.alloc_expr(expr, ptr)
    }

    fn lower_attrpath_opt(&mut self, attrpath: Option<ast::Attrpath>) -> Attrpath {
        attrpath
            .into_iter()
            .flat_map(|attrpath| attrpath.attrs())
            .map(|attr| match attr {
                ast::Attr::Dynamic(d) => self.lower_expr_opt(d.expr()),
                ast::Attr::Ident(ident) => {
                    let name = name_of_ident(&ident).expect("Should have a name");
                    let ptr = AstPtr::new(ident.syntax());
                    self.alloc_expr(Expr::Literal(Literal::String(name)), ptr)
                }
                ast::Attr::Str(s) => self.lower_string(s),
            })
            .collect()
    }

    fn lower_string(&mut self, s: rnix::ast::Str) -> ExprId {
        let ptr = AstPtr::new(s.syntax());

        let expr = if let Some(lit) = get_str_literal(&s) {
            Expr::Literal(Literal::String(lit))
        } else {
            let parts = s.normalized_parts();
            Expr::StringInterpolation(self.lower_interpolation(parts.into_iter()).collect())
        };
        self.alloc_expr(expr, ptr)
    }

    fn lower_interpolation_part<T: Clone>(
        &mut self,
        part: rnix::ast::InterpolPart<T>,
    ) -> InterpolPart<T> {
        match part {
            ast::InterpolPart::Literal(lit) => InterpolPart::Literal(lit),
            ast::InterpolPart::Interpolation(interpol) => {
                InterpolPart::Interpol(self.lower_expr_opt(interpol.expr()))
            }
        }
    }

    fn lower_interpolation<T: Clone>(
        &mut self,
        parts: impl Iterator<Item = rnix::ast::InterpolPart<T>>,
    ) -> impl Iterator<Item = InterpolPart<T>> {
        parts.map(|p| self.lower_interpolation_part(p))
    }

    fn lower_lambda(&mut self, lam: ast::Lambda, ptr: AstPtr) -> ExprId {
        // let mut param_locs = HashMap::new();
        let lower_name = |this: &mut Self, node: ast::Ident| -> NameId {
            let ptr = AstPtr::new(node.syntax());
            let text = name_of_ident(&node).expect("Should have name");
            this.alloc_name(text, ptr)
        };

        let (param, pat) = lam.param().map_or((None, None), |param| match param {
            ast::Param::IdentParam(ident_param) => {
                let param = ident_param.ident().map(|i| lower_name(self, i));
                (param, None)
            }
            ast::Param::Pattern(pattern) => {
                let param = pattern
                    .pat_bind()
                    .and_then(|ident_param| ident_param.ident())
                    .map(|i| lower_name(self, i));

                let fields = pattern
                    .pat_entries()
                    .map(|entry| {
                        let name = entry.ident().map(|i| lower_name(self, i));
                        let default_expr = entry.default().map(|e| self.lower_expr(e));

                        (name, default_expr)
                    })
                    .collect();

                let pat = Pat {
                    fields,
                    ellipsis: pattern.ellipsis_token().is_some(),
                };

                (param, Some(pat))
            }
        });
        let body = self.lower_expr_opt(lam.body());
        self.alloc_expr(Expr::Lambda { param, pat, body }, ptr)
    }
}

#[derive(Debug)]
struct MergingSet {
    ptr: AstPtr,
    statics: HashMap<String, MergingEntry>,
    inherit_froms: Vec<ExprId>,
    dynamics: Vec<(ExprId, ExprId)>,
}

#[derive(Debug)]
struct MergingEntry {
    /// The key of this entry.
    /// Used for tracking source map.
    name: NameId,
    /// The RHS if it is implicit or explicit set.
    /// We stores both `set` and `value` components to prevent information loss
    /// when handling duplicated keys.
    set: Option<MergingSet>,
    /// The RHS if it is not merge-able.
    /// The source location is for error reporting.
    value: Option<(AstPtr, BindingValue)>,
}

#[derive(Debug, Clone)]
pub enum BindingValueKind {
    Expr(Option<ast::Expr>),
    ImplicitSet, // TODO: handle this for real
    ExplicitSet(ast::AttrSet),
}

impl MergingSet {
    fn new(ptr: AstPtr) -> Self {
        Self {
            ptr,
            statics: HashMap::new(),
            inherit_froms: Vec::new(),
            dynamics: Vec::new(),
        }
    }

    fn desugar(ctx: &mut LowerCtx, node: &impl HasEntry) -> Self {
        let ptr = AstPtr::new(node.syntax());
        let mut this = Self::new(ptr);
        this.merge_bindings(ctx, node);
        this
    }

    fn merge_bindings(&mut self, ctx: &mut LowerCtx, node: &impl HasEntry) {
        for entry in node.entries() {
            match entry {
                ast::Entry::AttrpathValue(apv) => self.merge_attrpath_val(ctx, apv),
                ast::Entry::Inherit(inherit) => self.merge_inherit(ctx, inherit),
            }
        }
    }

    fn merge_attrpath_val(&mut self, ctx: &mut LowerCtx, apv: rnix::ast::AttrpathValue) {
        let value = BindingValueKind::Expr(apv.value());

        let attr_path = if let Some(apv) = apv.attrpath() {
            apv
        } else {
            return self.push_dynamic(ctx, None, value);
        };

        let mut attrs = attr_path.attrs();

        let attr = attrs
            .next()
            .expect("Should have at least one part of the attr key");

        if attrs.next().is_some() {
            // supporting this will require more merging logic i don't want to do yet
            todo!("Implicit attrs not support yet")
        }

        self.merge_attr_value(ctx, attr, value);
    }

    fn merge_inherit(&mut self, ctx: &mut LowerCtx, inherit: ast::Inherit) {
        let from_expr = inherit.from().map(|e| {
            let expr = ctx.lower_expr_opt(e.expr());
            let idx = self.inherit_froms.len();
            self.inherit_froms.push(expr);
            idx
        });

        if inherit.attrs().next().is_none() {
            eprintln!("TODO: No attrs on the inherit");
            return;
        }

        for attr in inherit.attrs() {
            let attr_ptr = AstPtr::new(attr.syntax());
            let key = match AttrKind::of(attr) {
                AttrKind::Static(key) => key.unwrap_or_default(),
                // `inherit ${expr}` or `inherit (expr) ${expr}` is invalid.
                AttrKind::Dynamic(expr) => {
                    // ctx.diagnostic(Diagnostic::new(
                    //     attr_ptr.text_range(),
                    //     DiagnosticKind::InvalidDynamic,
                    // ));
                    self.push_dynamic(ctx, None, BindingValueKind::Expr(expr));
                    continue;
                }
            };

            let value = match from_expr {
                Some(i) => BindingValue::InheritFrom(i),
                None => {
                    let ref_expr = ctx.alloc_expr(Expr::Reference(key.clone()), attr_ptr);
                    BindingValue::Inherit(ref_expr)
                }
            };
            self.merge_static_value(ctx, key, attr_ptr, value);
        }
    }

    fn merge_static_value(
        &mut self,
        ctx: &mut LowerCtx,
        key: String,
        attr_ptr: AstPtr,
        value: BindingValue,
    ) {
        self.statics
            .entry(key.clone())
            // Set-value or value-value collision.
            .and_modify(|ent| {
                todo!("Name collision! key: {key} ent: {:?}", ent)
                // Append this location to the existing name.
                // ctx.source_map.name_map.insert(attr_ptr, ent.name);
                // ctx.source_map.name_map_rev[ent.name].push(attr_ptr);

                // let prev_ptr = ctx.source_map.nodes_for_name(ent.name).next().unwrap();
                // ctx.diagnostic(
                //     Diagnostic::new(attr_ptr.text_range(), DiagnosticKind::DuplicatedKey)
                //         .with_note(
                //             FileRange::new(ctx.file_id, prev_ptr.text_range()),
                //             "Previously defined here",
                //         ),
                // );
            })
            .or_insert_with(|| MergingEntry {
                name: ctx.alloc_name(key, attr_ptr),
                set: None,
                value: Some((attr_ptr, value)),
            });
    }

    fn merge_attr_value(&mut self, ctx: &mut LowerCtx, attr: ast::Attr, value: BindingValueKind) {
        let attr_ptr = AstPtr::new(attr.syntax());

        match AttrKind::of(attr) {
            AttrKind::Static(key) => {
                let key = key.unwrap_or_default();
                match value {
                    BindingValueKind::Expr(e) => {
                        let e = ctx.lower_expr_opt(e);
                        self.merge_static_value(ctx, key, attr_ptr, BindingValue::Expr(e));
                    }
                    _ => todo!("handle other binding values"),
                }
            }
            AttrKind::Dynamic(key_expr) => {
                self.push_dynamic(ctx, key_expr, value);
            }
        }
    }

    fn push_dynamic(
        &mut self,
        ctx: &mut LowerCtx,
        key_expr: Option<ast::Expr>,
        value: BindingValueKind,
    ) {
        let key_expr = ctx.lower_expr_opt(key_expr);
        let value_expr = match value {
            BindingValueKind::Expr(e) => ctx.lower_expr_opt(e),
            _ => todo!("handle other binding values"),
        };
        self.dynamics.push((key_expr, value_expr));
    }

    fn finish(self, ctx: &mut LowerCtx) -> Bindings {
        Bindings {
            statics: self
                .statics
                .into_values()
                .map(|entry| {
                    let value = match entry.set {
                        Some(set) => todo!(), //BindingValue::Expr(set.finish_expr(ctx)),
                        None => entry.value.unwrap().1,
                    };
                    (entry.name, value)
                })
                .collect(),
            inherit_froms: self.inherit_froms.into(),
            dynamics: self.dynamics.into(),
        }
    }

    // fn finish_expr(mut self, ctx: &mut LowerCtx) -> ExprId {
    //     let ctor = match self.name_kind {
    //         // Implicit Attrsets can only be one of these two.
    //         NameKind::PlainAttrset => Expr::Attrset,
    //         NameKind::RecAttrset => Expr::RecAttrset,
    //         _ => unreachable!(),
    //     };
    //     let ptr = self.ptr.take();
    //     let e = ctor(self.finish(ctx));
    //     match ptr {
    //         Some(ptr) => ctx.alloc_expr(e, ptr),
    //         // For implicit Attrset produced by merging, there's no "source" for it.
    //         None => ctx.module.exprs.alloc(e),
    //     }
    // }
}
