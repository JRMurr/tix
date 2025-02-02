use std::collections::BTreeSet;

use derive_more::Debug;

use super::RefType;

// TODO: this is basically just a wrapper around BTreeSet
// doesn't add much other than adding intersection_with/union_with but those are just renames...
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Union<R: RefType> {
    set: BTreeSet<R>,
}

impl<R: RefType> Union<R> {
    pub fn new() -> Self {
        Self {
            set: BTreeSet::new(),
        }
    }

    pub fn intersection_with(&self, other: &Self) -> Self {
        let set = &self.set & &other.set;

        Self { set }
    }

    pub fn union_with(&self, other: &Self) -> Self {
        let set = &self.set | &other.set;

        Self { set }
    }

    pub fn remove(&mut self, value: &R) -> bool {
        self.set.remove(value)
    }

    pub fn contains(&self, value: &R) -> bool {
        self.set.contains(value)
    }

    pub fn is_super_set(&self, other: &Self) -> bool {
        self.set.is_superset(&other.set)
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.set.is_subset(&other.set)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.set.is_disjoint(&other.set)
    }

    pub fn iter(&self) -> std::collections::btree_set::Iter<'_, R> {
        self.set.iter()
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

impl<R: RefType> FromIterator<R> for Union<R> {
    fn from_iter<T: IntoIterator<Item = R>>(iter: T) -> Self {
        let set: BTreeSet<R> = iter.into_iter().collect();

        Self { set }
    }
}

impl<R: RefType, const N: usize> From<[R; N]> for Union<R> {
    fn from(value: [R; N]) -> Self {
        let set: BTreeSet<R> = value.into();

        Self { set }
    }
}
