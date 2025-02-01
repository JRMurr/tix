use std::collections::BTreeMap;

use derive_more::Debug;
use smol_str::SmolStr;

use crate::arc_ty::TyRef;

use super::Ty;

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct AttrSetTy<RefType> {
    // TODO: i think the value here needs to be a TyId or Schema
    pub fields: BTreeMap<SmolStr, RefType>,

    // TODO: this only allows for one dynamic field
    // once type level literals work we should support a map of these
    pub dyn_ty: Option<RefType>,

    // TODO: only really used in type inference
    // https://bernsteinbear.com/blog/row-poly/
    pub rest: Option<RefType>,
}

impl<RefType> AttrSetTy<RefType> {
    pub fn new() -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            rest: None,
        }
    }

    pub fn from_fields(fields: BTreeMap<SmolStr, RefType>) -> Self {
        Self {
            fields,
            dyn_ty: None,
            rest: None,
        }
    }

    pub fn from_rest(rest: RefType) -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            rest: Some(rest),
        }
    }

    pub fn keys(&self) -> std::collections::btree_map::Keys<'_, SmolStr, RefType> {
        self.fields.keys()
    }

    pub fn get(&self, key: &SmolStr) -> Option<&RefType> {
        self.fields.get(key)
    }
}

impl<RefType: Clone + Debug> AttrSetTy<RefType> {
    pub fn merge(self, other: Self) -> Self {
        // TODO: handle dyn_ty
        // TODO: not sure if this will always be the case but for now it is
        // assert!(
        //     self.rest.is_some(),
        //     "tried to merge but we don't have a rest type"
        // );
        // assert!(
        //     other.rest.is_none(),
        //     "tried to merge but other has a rest field still"
        // );

        // TODO: not sure if this should error if other has fields with the same key as self

        let mut fields: BTreeMap<SmolStr, RefType> = BTreeMap::new();

        for (k, v) in self.fields.iter().chain(other.fields.iter()) {
            fields.insert(k.clone(), v.clone());
        }

        Self {
            fields,
            dyn_ty: None, // TODO: handle
            rest: other.rest,
        }
    }

    pub fn get_sub_set(&self, keys: impl Iterator<Item = SmolStr>) -> Self {
        let mut fields = BTreeMap::new();
        for key in keys {
            let value = self
                .get(&key)
                .unwrap_or_else(|| panic!("Missing key {key}"));
            fields.insert(key, value.clone());
        }

        Self {
            fields,
            dyn_ty: self.dyn_ty.clone(),
            rest: self.rest.clone(),
        }
    }
}

impl AttrSetTy<TyRef> {
    pub fn from_internal<'a>(
        iter: impl IntoIterator<Item = (&'a str, Ty<TyRef>)>,
        rest: Option<TyRef>,
    ) -> Self {
        let fields: BTreeMap<SmolStr, TyRef> = iter
            .into_iter()
            .map(|(name, ty)| (SmolStr::from(name), ty.into()))
            .collect();
        // Arc::get_mut(&mut fields)
        //     .unwrap()
        //     .sort_by(|(lhs, ..), (rhs, ..)| lhs.cmp(rhs));
        // assert!(
        //     fields.windows(2).all(|w| w[0].0 != w[1].0),
        //     "Duplicated fields",
        // );
        Self {
            fields,
            rest,
            dyn_ty: None,
        }
    }
}
