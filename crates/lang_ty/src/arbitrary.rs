use crate::{ArcTy, AttrSetTy, PrimitiveTy, Substitutions, TyRef};
use proptest::{
    prelude::{any, prop, prop_oneof, Arbitrary, BoxedStrategy, Just, Strategy},
    prop_compose,
};
use smol_str::SmolStr;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveParams {
    pub depth: u32,
    pub desired_size: u32,
    pub expected_branch_size: u32,
}

fn arb_arc_ty(args: RecursiveParams) -> impl Strategy<Value = ArcTy> {
    let leaf = any::<PrimitiveTy>().prop_map(ArcTy::Primitive);

    leaf.prop_recursive(
        args.depth,
        args.desired_size,
        args.expected_branch_size,
        |inner| {
            let inner = inner.prop_map(TyRef::from);

            prop_oneof![
                inner.clone().prop_map(ArcTy::List),
                (inner.clone(), inner.clone())
                    .prop_map(|(param, body)| ArcTy::Lambda { param, body }),
                prop::collection::btree_map(arb_smol_str_ident(), inner.clone(), 0..5)
                    .prop_map(|map| ArcTy::AttrSet(AttrSetTy::from_fields(map)))
            ]
        },
    )
}

prop_compose! {
    // put a 10 char limit on identifiers, should be enough....
    pub fn arb_smol_str_ident()(string in "_pbt_([a-z]|[A-Z]|[0-9]|_){1,10}") -> SmolStr {
        string.into()
    }
}

impl Default for RecursiveParams {
    fn default() -> Self {
        // TODO: picked basically at random...
        Self {
            depth: 4,                // levels deep
            desired_size: 64,        // total nodes
            expected_branch_size: 3, // items per collection
        }
    }
}

impl Arbitrary for ArcTy {
    type Parameters = RecursiveParams;
    type Strategy = BoxedStrategy<ArcTy>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        arb_arc_ty(args).boxed()
    }
}

pub fn arb_prim() -> impl Strategy<Value = PrimitiveTy> {
    prop_oneof![
        Just(PrimitiveTy::Null),
        Just(PrimitiveTy::Bool),
        Just(PrimitiveTy::Int),
        Just(PrimitiveTy::Float),
        Just(PrimitiveTy::String),
        // Just(PrimitiveTy::Path),
        // no uri
    ]
    .boxed()
}

impl Arbitrary for PrimitiveTy {
    type Parameters = ();
    type Strategy = BoxedStrategy<PrimitiveTy>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_prim().boxed()
    }
}

impl AttrSetTy<TyRef> {
    /// Each child of the attrset for now will be unique
    /// so we need to make sure each child has its own unique ty vars
    pub fn spread_free_vars(&self, num_free_vars: &mut usize) -> Self {
        // let mut num_free_vars = 0;

        let fields = self
            .fields
            .iter()
            .map(|(k, v)| {
                let free_vars = v.0.free_type_vars();

                let subs: Substitutions = free_vars
                    .iter()
                    .enumerate()
                    .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
                    .collect();

                *num_free_vars += free_vars.len();

                let ty = v.0.normalize_inner(&subs).into();

                (k.clone(), ty)
            })
            .collect();

        // let dyn_ty = self
        //     .dyn_ty
        //     .clone()
        //     .map(|dyn_ty| dyn_ty.0.normalize_inner(free).into());

        // let rest = self
        //     .rest
        //     .clone()
        //     .map(|rest| rest.0.normalize_inner(free).into());

        Self {
            fields,
            dyn_ty: None, // TODO:
            rest: None,   // TODO:
        }
    }
}

impl ArcTy {
    // TODO: make spread_free_vars for all variants
    pub fn offset_free_vars(&self, num_free_vars: &mut usize) -> Self {
        let free_vars = self.free_type_vars();

        // TODO: extract this
        let subs: Substitutions = free_vars
            .iter()
            .enumerate()
            .map(|(i, var)| (*var, (*num_free_vars + i + 1) as u32))
            .collect();

        *num_free_vars += free_vars.len();

        self.normalize_inner(&subs)
    }
}
