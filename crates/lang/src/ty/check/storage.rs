use std::collections::HashMap;

use union_find::{QuickFindUf, UnionByRank, UnionFind};

use crate::Ty;

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

#[derive(Debug, Clone)]
pub struct TypeStorage {
    pub(crate) uf: QuickFindUf<UnionByRank>,
    pub(crate) types: HashMap<TyId, Ty<TyId>>,
}

impl TypeStorage {
    pub fn new() -> Self {
        Self {
            uf: QuickFindUf::new(0),
            types: HashMap::new(),
        }
    }

    pub fn find(&mut self, id: TyId) -> TyId {
        self.uf.find(id.into()).into()
    }

    pub fn new_ty(&mut self) -> TyId {
        self.uf.insert(UnionByRank::default()).into()
    }

    pub fn insert(&mut self, val: Ty<TyId>) -> TyId {
        let key = self.new_ty();

        self.types.insert(key, val);

        key
    }

    pub fn get(&mut self, id: TyId) -> Option<Ty<TyId>> {
        let root = self.find(id);

        self.types.get(&root).cloned()
    }

    pub fn unify(&mut self, lhs: TyId, rhs: TyId, new_val: Ty<TyId>) {
        let lhs = self.find(lhs);
        let rhs = self.find(rhs);

        let root = if self.uf.union(lhs.into(), rhs.into()) {
            // table did a union, need to clean up the type table
            self.types.remove(&lhs);
            self.types.remove(&rhs);

            // get new root
            self.find(lhs)
        } else {
            // no union can just use either key
            lhs
        };

        let is_ty_var = matches!(new_val, Ty::TyVar(_));

        if !is_ty_var {
            self.types.insert(root, new_val);
        }
    }
}
