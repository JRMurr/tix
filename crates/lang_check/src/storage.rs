use std::collections::HashSet;

use lang_ty::{union::Union, Ty};
use union_find::{QuickFindUf, UnionByRank, UnionFind};

// use ena::unify::{InPlaceUnificationTable, UnifyKey};
use rustc_hash::FxHashMap;
// use union_find::{QuickFindUf, UnionByRank};

use crate::RootConstraint;

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

type TyMapping = FxHashMap<TyId, Ty<TyId>>;

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

        self.flatten_inner(root, &mut HashSet::default());
    }

    /// if ty_id is a union recursively unify all inner unions to flatten it out
    pub fn flatten(&mut self, ty_id: TyId) -> (TyId, Option<Ty<TyId>>) {
        self.flatten_inner(ty_id, &mut HashSet::default());
        self.get_root_value(ty_id)
        // match self.flatten_inner(ty_id, &mut HashSet::default()) {
        //     Some((root, _)) => self.types.get(&root).cloned(),
        //     _ => self.get_root_value(ty_id),
        // }
    }

    /// Returns the root id of the flattened union (if TyId was a union)
    fn flatten_inner(
        &mut self,
        ty_id: TyId,
        seen: &mut HashSet<TyId>,
    ) -> Option<(TyId, Union<TyId>)> {
        let (ty_id, ty) = self.get_root_value(ty_id);

        let Some(Ty::Union(inner)) = ty else {
            return None;
        };

        if seen.contains(&ty_id) {
            // dbg!(&ty_id, &inner, &seen, self.root_type_view());
            // return None;
            panic!("cycle in union flattening")
        }

        seen.insert(ty_id);

        let mut inner: Union<TyId> = inner.iter().map(|t| self.find(*t)).collect();

        // remove any refs to itself to avoid cycles
        // TODO: not sure if this will catch all cases but good for now
        inner.remove(&ty_id);

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
            self.get(ty_id)
        } else {
            Some(Ty::Union(inner.clone()))
        };

        if let Some(v) = val {
            self.types.insert(root, v);
        }

        // can still return the inner union in the single value case for recursion
        Some((root, inner))
    }

    fn root_ty(&mut self, ty: &Ty<TyId>) -> Ty<TyId> {
        match ty {
            Ty::TyVar(id) => Ty::TyVar(self.find((*id).into()).0),
            Ty::Primitive(primitive_ty) => Ty::Primitive(*primitive_ty),
            Ty::List(inner) => Ty::List(self.find(*inner)),
            Ty::Lambda { param, body } => Ty::Lambda {
                param: self.find(*param),
                body: self.find(*body),
            },
            Ty::AttrSet(inner) => Ty::AttrSet(inner.map_values(|id| self.find(id))),
            Ty::Union(union) => Ty::Union(union.iter().map(|i| self.find(*i)).collect()),
        }
    }

    pub fn check_eq(&mut self, lhs: TyId, rhs: TyId) -> bool {
        self.check_eq_inner(lhs, rhs, &mut FxHashMap::default())
    }

    // Check if two types are "structurally" equal
    // that is the right side could be come the left side by replacing the free vars correctly
    // we store mappings in var_mapping like
    // [left_side_ty] => right_side_ty
    // INVARIANT: this should be called after solving so all ty-vars seen are free vars
    fn check_eq_inner(
        &mut self,
        lhs: TyId,
        rhs: TyId,
        var_mapping: &mut FxHashMap<TyId, TyId>,
    ) -> bool {
        let (lhs, lhs_ty) = self.get_root_value(lhs);
        let (rhs, rhs_ty) = self.get_root_value(rhs);

        let (Some(lhs_ty), Some(rhs_ty)) = (lhs_ty, rhs_ty) else {
            return false;
        };

        match (lhs_ty, rhs_ty) {
            (Ty::Primitive(l), Ty::Primitive(r)) => l == r,
            (Ty::TyVar(l), Ty::TyVar(r)) => {
                let l = self.find(l.into());
                let r = self.find(r.into());

                // they are the same so no need to do anything
                if l == r {
                    return true;
                }

                // if we stored a mapping from the left side to the right side
                // check if the replacement still holds
                if let Some(val) = var_mapping.get(&l) {
                    return *val == r;
                }

                // newly seen free var
                // add it to the mapping to make sure it holds elsewhere

                var_mapping.insert(l, r);

                true
            }
            (Ty::List(l), Ty::List(r)) => self.check_eq_inner(l, r, var_mapping),
            (Ty::AttrSet(l), Ty::AttrSet(r)) => {
                todo!();
            }
            (Ty::Union(a), Ty::Union(b)) => {
                todo!();
            }
            _ => false,
        }
    }

    #[allow(dead_code)]
    pub fn root_constraint_view(&mut self, constraint: &RootConstraint) -> RootConstraint {
        RootConstraint {
            kind: constraint.kind.map(|ty_id| self.find(ty_id)),
            location: constraint.location,
        }
    }

    #[allow(dead_code)]
    pub fn root_type_view(&mut self) -> TyMapping {
        self.types
            .clone()
            .iter()
            .map(|(key, ty)| {
                let ty = self.root_ty(ty);

                (*key, ty)
            })
            .collect()
    }

    #[allow(dead_code)]
    pub fn debug_get_union_inner(&mut self, ty_id: TyId) -> Vec<Ty<TyId>> {
        let Some(Ty::Union(union)) = self.get(ty_id) else {
            return Vec::new();
        };

        union
            .iter()
            .map(|t| self.get(*t).unwrap_or(Ty::TyVar(t.0)))
            .collect()
    }
}
