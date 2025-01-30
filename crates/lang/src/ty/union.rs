use std::collections::BTreeSet;

use derive_more::Debug;

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Union<RefType> {
    set: BTreeSet<RefType>,
}

impl<RefType> Union<RefType> {}
