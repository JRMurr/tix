use std::collections::BTreeMap;

use derive_more::Debug;
use smol_str::SmolStr;

use crate::arc_ty::TyRef;

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct AttrSetTy<RefType> {
    pub fields: BTreeMap<SmolStr, RefType>,

    // TODO: this only allows for one dynamic field
    // once type level literals work we should support a map of these
    pub dyn_ty: Option<RefType>,

    /// Whether this attrset accepts additional fields beyond those listed.
    /// `true` means "open" (e.g. a pattern with `...`), `false` means "exactly these fields".
    /// Replaces the old row-polymorphism `rest` field — with structural subtyping,
    /// width subtyping handles the cases that row variables used to cover.
    pub open: bool,
}

impl<RefType> AttrSetTy<RefType> {
    pub fn new() -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            open: false,
        }
    }

    pub fn from_fields(fields: BTreeMap<SmolStr, RefType>) -> Self {
        Self {
            fields,
            dyn_ty: None,
            open: false,
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
    /// Merge two attrsets. Fields from `other` override fields from `self` (right-biased).
    pub fn merge(self, other: Self) -> Self {
        let mut fields: BTreeMap<SmolStr, RefType> = BTreeMap::new();

        for (k, v) in self.fields.iter().chain(other.fields.iter()) {
            fields.insert(k.clone(), v.clone());
        }

        Self {
            fields,
            dyn_ty: None, // TODO: handle
            open: self.open || other.open,
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
            open: self.open,
        }
    }
}

impl AttrSetTy<TyRef> {
    pub fn from_internal<'a>(
        iter: impl IntoIterator<Item = (&'a str, crate::OutputTy)>,
        open: bool,
    ) -> Self {
        let fields: BTreeMap<SmolStr, TyRef> = iter
            .into_iter()
            .map(|(name, ty)| (SmolStr::from(name), ty.into()))
            .collect();
        Self {
            fields,
            open,
            dyn_ty: None,
        }
    }
}
