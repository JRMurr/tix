use std::collections::BTreeSet;

use derive_more::Debug;

use super::RefType;

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
}

impl<R: RefType> FromIterator<R> for Union<R> {
    fn from_iter<T: IntoIterator<Item = R>>(iter: T) -> Self {
        let set: BTreeSet<R> = iter.into_iter().collect();

        Self { set }
    }
}
