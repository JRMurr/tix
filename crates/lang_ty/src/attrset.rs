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
    pub open: bool,

    /// Fields that may be omitted by the caller because they have default values.
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
        let mut optional = self.optional_fields;
        for key in other.fields.keys() {
            if !other.optional_fields.contains(key) {
                optional.remove(key);
            }
        }
        optional.extend(other.optional_fields);

        let mut fields = self.fields;
        for (k, v) in other.fields {
            fields.insert(k, v);
        }

        Self {
            fields,
            dyn_ty: other.dyn_ty.or(self.dyn_ty),
            open: self.open || other.open,
            optional_fields: optional,
        }
    }
}

impl PartialOrd for AttrSetTy<TyRef> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AttrSetTy<TyRef> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.fields
            .cmp(&other.fields)
            .then_with(|| self.dyn_ty.cmp(&other.dyn_ty))
            .then_with(|| self.open.cmp(&other.open))
            .then_with(|| self.optional_fields.cmp(&other.optional_fields))
    }
}

impl AttrSetTy<TyRef> {
    /// Build an AttrSetTy from pre-interned TyRef children.
    pub fn from_internal<'a>(iter: impl IntoIterator<Item = (&'a str, TyRef)>, open: bool) -> Self {
        let fields: BTreeMap<SmolStr, TyRef> = iter
            .into_iter()
            .map(|(name, ty)| (SmolStr::from(name), ty))
            .collect();
        Self {
            fields,
            open,
            dyn_ty: None,
            optional_fields: BTreeSet::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{arc_ty, TypeArena};

    /// Helper: build a simple closed AttrSetTy from field name-type pairs using an arena.
    fn make_attrset(arena: &mut TypeArena, fields: &[(&str, crate::OutputTy)]) -> AttrSetTy<TyRef> {
        let map: BTreeMap<SmolStr, TyRef> = fields
            .iter()
            .map(|(k, v)| (SmolStr::from(*k), arena.intern(v.clone())))
            .collect();
        AttrSetTy {
            fields: map,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }
    }

    #[test]
    fn merge_non_overlapping() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let str_ref = arc_ty!(&mut arena, String);
        let a = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        let b = make_attrset(
            &mut arena,
            &[("y", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        let merged = a.merge(b);
        assert_eq!(merged.fields.len(), 2);
        assert_eq!(merged.fields["x"], int_ref);
        assert_eq!(merged.fields["y"], str_ref);
    }

    #[test]
    fn merge_overlapping_right_wins() {
        let mut arena = TypeArena::new();
        let str_ref = arc_ty!(&mut arena, String);
        let a = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        let b = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        let merged = a.merge(b);
        assert_eq!(merged.fields.len(), 1);
        assert_eq!(merged.fields["x"], str_ref);
    }

    #[test]
    fn merge_optional_becomes_required() {
        let mut arena = TypeArena::new();
        let str_ref = arc_ty!(&mut arena, String);
        let mut a = make_attrset(
            &mut arena,
            &[("y", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        a.optional_fields.insert(SmolStr::from("y"));
        let b = make_attrset(
            &mut arena,
            &[("y", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        let merged = a.merge(b);
        assert!(
            !merged.optional_fields.contains("y"),
            "y should be required after merge with required y"
        );
        assert_eq!(merged.fields["y"], str_ref);
    }

    #[test]
    fn merge_required_stays_in_other_optional() {
        let mut arena = TypeArena::new();
        let str_ref = arc_ty!(&mut arena, String);
        let a = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        let mut b = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        b.optional_fields.insert(SmolStr::from("x"));
        let merged = a.merge(b);
        assert!(
            merged.optional_fields.contains("x"),
            "x should be optional because other marks it optional"
        );
        assert_eq!(merged.fields["x"], str_ref);
    }

    #[test]
    fn merge_both_optional() {
        let mut arena = TypeArena::new();
        let mut a = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        a.optional_fields.insert(SmolStr::from("x"));
        let mut b = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        b.optional_fields.insert(SmolStr::from("x"));
        let merged = a.merge(b);
        assert!(
            merged.optional_fields.contains("x"),
            "x should stay optional when both sides are optional"
        );
    }

    #[test]
    fn merge_dyn_ty_right_only() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let a = make_attrset(&mut arena, &[]);
        let mut b = make_attrset(&mut arena, &[]);
        b.dyn_ty = Some(int_ref);
        let merged = a.merge(b);
        assert_eq!(merged.dyn_ty, Some(int_ref));
    }

    #[test]
    fn merge_dyn_ty_left_only() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let mut a = make_attrset(&mut arena, &[]);
        a.dyn_ty = Some(int_ref);
        let b = make_attrset(&mut arena, &[]);
        let merged = a.merge(b);
        assert_eq!(merged.dyn_ty, Some(int_ref));
    }

    #[test]
    fn merge_dyn_ty_both_right_wins() {
        let mut arena = TypeArena::new();
        let int_ref = arc_ty!(&mut arena, Int);
        let str_ref = arc_ty!(&mut arena, String);
        let mut a = make_attrset(&mut arena, &[]);
        a.dyn_ty = Some(int_ref);
        let mut b = make_attrset(&mut arena, &[]);
        b.dyn_ty = Some(str_ref);
        let merged = a.merge(b);
        assert_eq!(merged.dyn_ty, Some(str_ref));
    }

    #[test]
    fn merge_open_if_either_open() {
        let mut arena = TypeArena::new();
        let closed = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        let mut open = make_attrset(
            &mut arena,
            &[("y", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        open.open = true;

        let merged1 = closed.clone().merge(open.clone());
        assert!(merged1.open, "closed.merge(open) should be open");

        let merged2 = open.merge(closed);
        assert!(merged2.open, "open.merge(closed) should be open");
    }

    #[test]
    fn merge_both_closed_stays_closed() {
        let mut arena = TypeArena::new();
        let a = make_attrset(
            &mut arena,
            &[("x", crate::OutputTy::Primitive(crate::PrimitiveTy::Int))],
        );
        let b = make_attrset(
            &mut arena,
            &[("y", crate::OutputTy::Primitive(crate::PrimitiveTy::String))],
        );
        let merged = a.merge(b);
        assert!(!merged.open, "closed.merge(closed) should stay closed");
    }
}

#[cfg(test)]
mod hegel_tests {
    use super::*;
    use hegel::generators;
    use hegel::TestCase;

    /// `AttrSetTy` is generic over the field payload; `u32` keeps the laws
    /// about the container itself, not the types inside.
    type Attrs = AttrSetTy<u32>;

    const MAX_FIELDS: usize = 6;

    #[hegel::composite]
    fn attrs(tc: &TestCase) -> Attrs {
        // Small key alphabet so that two drawn attrsets usually overlap.
        let keys: Vec<&str> = tc.draw(
            generators::vecs(generators::sampled_from(vec!["a", "b", "c", "d", "e"]))
                .max_size(MAX_FIELDS)
                .unique(true),
        );
        let mut fields = BTreeMap::new();
        let mut optional_fields = BTreeSet::new();
        for k in keys {
            fields.insert(SmolStr::from(k), tc.draw(generators::integers::<u32>()));
            if tc.draw(generators::booleans()) {
                optional_fields.insert(SmolStr::from(k));
            }
        }
        Attrs {
            fields,
            dyn_ty: tc.draw(generators::optional(generators::integers::<u32>())),
            open: tc.draw(generators::booleans()),
            optional_fields,
        }
    }

    #[hegel::test]
    fn merge_idempotent(tc: TestCase) {
        let a = tc.draw(attrs());
        assert_eq!(a.clone().merge(a.clone()), a);
    }

    #[hegel::test]
    fn merge_empty_is_identity(tc: TestCase) {
        let a = tc.draw(attrs());
        assert_eq!(Attrs::new().merge(a.clone()), a);
        assert_eq!(a.clone().merge(Attrs::new()), a);
    }

    #[hegel::test]
    fn merge_associative(tc: TestCase) {
        let a = tc.draw(attrs());
        let b = tc.draw(attrs());
        let c = tc.draw(attrs());
        let left = a.clone().merge(b.clone()).merge(c.clone());
        let right = a.merge(b.merge(c));
        assert_eq!(left, right);
    }

    #[hegel::test]
    fn merge_right_biased_with_key_union(tc: TestCase) {
        let a = tc.draw(attrs());
        let b = tc.draw(attrs());
        let merged = a.clone().merge(b.clone());

        let expected_keys: BTreeSet<&SmolStr> = a.keys().chain(b.keys()).collect();
        let actual_keys: BTreeSet<&SmolStr> = merged.keys().collect();
        assert_eq!(actual_keys, expected_keys);

        for (k, v) in &merged.fields {
            let expected = b.get(k).or_else(|| a.get(k)).unwrap();
            assert_eq!(v, expected, "field {k}");
        }
        assert_eq!(merged.open, a.open || b.open);
        assert_eq!(merged.dyn_ty, b.dyn_ty.or(a.dyn_ty));
    }

    /// A field is optional after the merge iff its last contributor made it optional.
    #[hegel::test]
    fn merge_optional_follows_last_writer(tc: TestCase) {
        let a = tc.draw(attrs());
        let b = tc.draw(attrs());
        let merged = a.clone().merge(b.clone());

        for k in merged.keys() {
            let expected = if b.fields.contains_key(k) {
                b.optional_fields.contains(k)
            } else {
                a.optional_fields.contains(k)
            };
            assert_eq!(merged.optional_fields.contains(k), expected, "field {k}");
        }
    }
}
