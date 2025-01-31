use std::collections::{BTreeMap, HashMap};

use smol_str::SmolStr;

use super::{CheckCtx, InferenceResult, TyId};
use lang_ty::{ArcTy, AttrSetTy, Substitutions, Ty, TyRef};

pub struct Collector<'db> {
    cache: HashMap<TyId, ArcTy>,
    ctx: CheckCtx<'db>,
}

impl<'db> Collector<'db> {
    pub fn new(ctx: CheckCtx<'db>) -> Self {
        Self {
            cache: HashMap::with_capacity(ctx.table.types.len()),
            ctx,
        }
    }

    pub fn finalize_inference(&mut self) -> InferenceResult {
        let ctx = &mut self.ctx;

        let name_tys: Vec<_> = ctx
            .module
            .names()
            .map(|(name, _)| {
                // TODO: i think this is causing a new instantiation?
                // let ty = ctx.ty_for_name(name);
                // dbg!(&(name, name_txt));
                let ty = u32::from(name.into_raw()).into();
                (name, ty)
            })
            .collect();

        let expr_tys: Vec<_> = ctx
            .module
            .exprs()
            .map(|(expr, _)| {
                let ty = ctx.ty_for_expr(expr);
                (expr, ty)
            })
            .collect();

        let name_cnt = ctx.module.names().len();
        let expr_cnt = ctx.module.exprs().len();
        let mut name_ty_map = HashMap::with_capacity(name_cnt);
        let mut expr_ty_map = HashMap::with_capacity(expr_cnt);
        for (name, ty) in name_tys {
            // let free_vars = ctx
            //     .poly_type_env
            //     .get(&name)
            //     .expect("Should have generalized all names by now");
            let ty = self.canonicalize_type(ty, &HashMap::default());
            name_ty_map.insert(name, ty.normalize_vars());
        }
        for (expr, ty) in expr_tys {
            let mut ty = self.canonicalize_type(ty, &HashMap::default());

            if expr == self.ctx.module.entry_expr {
                ty = ty.normalize_vars();
            }

            expr_ty_map.insert(expr, ty);
        }

        dbg!(&self.ctx.table);

        InferenceResult {
            name_ty_map,
            expr_ty_map,
        }
    }

    fn canonicalize_type(&mut self, ty: TyId, subs: &Substitutions) -> ArcTy {
        let i = self.ctx.table.find(ty);
        if let Some(ty) = self.cache.get(&i).cloned() {
            return ty;
        }

        let ret = self.canonicalize_type_uncached(ty, subs);
        self.cache.insert(i, ret.clone());
        ret
    }

    fn canonicalize_type_uncached(&mut self, ty_id: TyId, subs: &Substitutions) -> ArcTy {
        // let ty = self.ctx.get_ty(ty_id);
        let ty_id = self.ctx.table.find(ty_id);
        let ty = self.ctx.get_ty(ty_id);

        // let ty = if let Some(t) = ty {
        //     t
        // } else {
        //     let root = self.ctx.table.find(ty_id);
        //     // eprintln!("{ty_id:?} is unknown\troot: {root:?}");
        //     Ty::TyVar(root.0)
        // };

        match ty {
            Ty::TyVar(x) => {
                // TODO: this should just be a generic param at this point
                // should eventually normalize the vars so they start from 0
                // could maybe do that as a final pass on the name?
                ArcTy::TyVar(x)
                // if x != ty_id.0 {
                //     self.canonicalize_type(TyId::from(x))
                // } else {
                //     ArcTy::TyVar(x)
                // }
            }
            Ty::List(inner_id) => {
                let c_inner = self.canonicalize_type(inner_id, subs);
                ArcTy::List(c_inner.into())
            }
            Ty::Lambda { param, body } => {
                let c_param = self.canonicalize_type(param, subs).into();
                let c_body = self.canonicalize_type(body, subs).into();
                ArcTy::Lambda {
                    param: c_param,
                    body: c_body,
                }
            }
            Ty::AttrSet(attr_set_ty) => {
                // let c_attr = self.canonicalize_attrset(attr_set_ty);
                // ArcTy::AttrSet(c_attr)
                // ArcTy::AttrSet(AttrSetTy {
                //     fields: BTreeMap::new(),
                //     dyn_ty: None,
                //     rest: None,
                // })
                self.canonicalize_attrset(attr_set_ty, subs)
            }
            Ty::Primitive(p) => ArcTy::Primitive(p),
            Ty::Union(inner) => Ty::Union(
                inner
                    .iter()
                    .map(|v| self.canonicalize_type(*v, subs).into())
                    .collect(),
            ),
        }
    }

    fn canonicalize_attrset(
        &mut self,
        attr_set_ty: AttrSetTy<TyId>,
        subs: &Substitutions,
    ) -> ArcTy {
        let mut new_fields = BTreeMap::<SmolStr, TyRef>::new();
        for (k, &v_id) in &attr_set_ty.fields {
            let field_ty = self.canonicalize_type(v_id, subs).into();
            new_fields.insert(k.clone(), field_ty);
        }
        let dyn_ty = attr_set_ty
            .dyn_ty
            .map(|d_id| self.canonicalize_type(d_id, subs).into());

        let rest = attr_set_ty
            .rest
            .map(|r_id| self.canonicalize_type(r_id, subs));

        // TODO: not sure if still needs this explicit merge
        // also need to figure out how to track "open" records like patterns
        // right now if the rest points to an "unknown" type var not sure if that means it would be closed
        // thats the case for row_poly.nix
        match rest {
            Some(Ty::AttrSet(other)) => {
                let curr = AttrSetTy {
                    fields: new_fields,
                    dyn_ty,
                    rest: None,
                };

                ArcTy::AttrSet(curr.merge(other))
            }
            _ => ArcTy::AttrSet(AttrSetTy {
                fields: new_fields,
                dyn_ty,
                rest: rest.map(|r| r.into()),
            }),
        }
    }
}
