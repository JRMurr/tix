use std::collections::HashSet;

use union_find::{QuickFindUf, UnionByRank, UnionFind};

// use ena::unify::{InPlaceUnificationTable, UnifyKey};
use rustc_hash::FxHashMap;
// use union_find::{QuickFindUf, UnionByRank};

use crate::{ty::union::Union, Ty};

use super::TyId;

// #[derive(Clone, Debug)]
// pub enum TypeVariableValue {
//     Known(Ty<TyId>),
//     Unknown,
// }

// impl TypeVariableValue {
//     /// If this value is known, returns the type it is known to be.
//     /// Otherwise, `None`.
//     pub(crate) fn known(&self) -> Option<Ty<TyId>> {
//         match self {
//             TypeVariableValue::Unknown => None,
//             TypeVariableValue::Known(value) => Some(value.clone()),
//         }
//     }

//     #[allow(dead_code)]
//     pub(crate) fn is_unknown(&self) -> bool {
//         match *self {
//             TypeVariableValue::Unknown => true,
//             TypeVariableValue::Known { .. } => false,
//         }
//     }
// }

// impl UnifyKey for TyId {
//     type Value = ();

//     fn index(&self) -> u32 {
//         self.0
//     }

//     fn from_index(u: u32) -> Self {
//         TyId(u)
//     }

//     fn tag() -> &'static str {
//         "TyId"
//     }
// }

#[derive(Debug, Clone)]
pub struct TypeStorage {
    pub(crate) uf: QuickFindUf<UnionByRank>,
    pub(crate) types: FxHashMap<TyId, Ty<TyId>>,
}

impl TypeStorage {
    pub fn new() -> Self {
        Self {
            uf: QuickFindUf::new(0), //InPlaceUnificationTable::new(), // QuickFindUf::new(0),
            types: FxHashMap::default(),
        }
    }

    pub fn find(&mut self, id: TyId) -> TyId {
        self.uf.find(id.into()).into()
    }

    pub fn new_ty(&mut self) -> TyId {
        self.uf.insert(UnionByRank::default()).into()
        // self.uf.new_key(())
    }

    pub fn insert(&mut self, val: Ty<TyId>) -> TyId {
        let key = self.new_ty();

        self.types.insert(key, val);

        key
    }

    pub fn get(&mut self, id: TyId) -> Option<Ty<TyId>> {
        self.get_root_value(id).1
    }

    pub fn get_root_value(&mut self, id: TyId) -> (TyId, Option<Ty<TyId>>) {
        let root = self.find(id);

        let val = self.types.get(&root).cloned();

        (root, val)
    }

    pub fn unify(&mut self, lhs: TyId, rhs: TyId, new_val: Ty<TyId>) {
        let lhs = self.find(lhs);
        let rhs = self.find(rhs);

        let root = if lhs == rhs {
            lhs
        } else {
            // self.uf.union(lhs, rhs);
            self.uf.union(lhs.into(), rhs.into());
            self.types.remove(&lhs);
            self.types.remove(&rhs);
            self.find(lhs)
        };

        let is_ty_var = matches!(new_val, Ty::TyVar(_));

        if !is_ty_var {
            self.types.insert(root, new_val);
        }
    }

    /// if ty_id is a union recursively unify all inner unions to flatten it out
    pub fn flatten(&mut self, ty_id: TyId) -> Option<Ty<TyId>> {
        // self.flatten_inner(ty_id);
        match self.flatten_inner(ty_id, &mut HashSet::default()) {
            Some((root, _)) => self.types.get(&root).cloned(),
            _ => self.get(ty_id),
        }
    }

    /// Returns the root id of the flattened union (if TyId was a union)
    fn flatten_inner(
        &mut self,
        ty_id: TyId,
        seen: &mut HashSet<TyId>,
    ) -> Option<(TyId, Union<TyId>)> {
        let (ty_id, ty) = self.get_root_value(ty_id);

        if seen.contains(&ty_id) {
            return None;
        }

        seen.insert(ty_id);

        let Some(Ty::Union(inner)) = ty else {
            return None;
        };

        let mut inner: Union<TyId> = inner.iter().map(|t| self.find(*t)).collect();

        let mut inner_unions = Vec::with_capacity(inner.len());

        // TODO: need to track seen to avoid cycles
        for child in inner.iter() {
            if let Some(child_union) = self.flatten_inner(*child, seen) {
                inner_unions.push(child_union);
            }
        }

        for (child_id, child_union) in inner_unions {
            inner.remove(&child_id);
            self.types.remove(&child_id);
            inner = inner.union_with(&child_union);

            self.uf.union(ty_id.into(), child_id.into());
        }

        self.types.remove(&ty_id);

        let root = self.find(ty_id);

        // only a union wth one element so we can just use that value to set
        let val = if inner.len() == 1 {
            let ty_id = inner.iter().next().cloned().unwrap();
            Ty::TyVar(ty_id.0)
        } else {
            Ty::Union(inner.clone())
        };

        self.types.insert(root, val);

        // can still return the inner union in the single value case for recursion
        Some((root, inner))
    }
}
