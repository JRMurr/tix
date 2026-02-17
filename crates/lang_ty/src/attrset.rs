use std::collections::{BTreeMap, BTreeSet};

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

    /// Fields that may be omitted by the caller because they have default values.
    /// Only meaningful for attrsets derived from lambda pattern parameters
    /// (e.g. `{ x, y ? 0 }: ...` marks `y` as optional).
    pub optional_fields: BTreeSet<SmolStr>,
}

impl<RefType> AttrSetTy<RefType> {
    pub fn new() -> Self {
        Self {
            fields: Default::default(),
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }
    }

    pub fn from_fields(fields: BTreeMap<SmolStr, RefType>) -> Self {
        Self {
            fields,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
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

        // Right-biased merge for optional_fields: start with self's optional set,
        // remove keys that are concretely provided in `other` (they become required
        // in the merged result), then union with other's optional set.
        let mut optional = self.optional_fields.clone();
        for key in other.fields.keys() {
            if !other.optional_fields.contains(key) {
                optional.remove(key);
            }
        }
        optional.extend(other.optional_fields.iter().cloned());

        Self {
            fields,
            // Right-biased merge: Nix `//` gives priority to the right-hand side.
            // We can't unify both dyn_ty values here (no constraint allocator),
            // so right-biased is the correct approximation.
            dyn_ty: other.dyn_ty.or(self.dyn_ty),
            open: self.open || other.open,
            optional_fields: optional,
        }
    }

    pub fn get_sub_set(&self, keys: impl Iterator<Item = SmolStr>) -> Self {
        let mut fields = BTreeMap::new();
        let mut optional = BTreeSet::new();
        for key in keys {
            let value = self
                .get(&key)
                .unwrap_or_else(|| panic!("Missing key {key}"));
            fields.insert(key.clone(), value.clone());
            if self.optional_fields.contains(&key) {
                optional.insert(key);
            }
        }

        Self {
            fields,
            dyn_ty: self.dyn_ty.clone(),
            open: self.open,
            optional_fields: optional,
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
            optional_fields: BTreeSet::new(),
        }
    }
}
