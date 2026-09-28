//! Pith structural type interner: [`TypeStore`] + [`TypeData`].
//!
//! The store hash-conses structural types into stable [`TypeId`] identities:
//! interning identical structures always yields identical ids, so types are
//! cheap to copy, compare, and key caches on.
//!
//! Design law (H-002, confirmed by PITH-E001): NO occurrence-varying state may
//! enter [`TypeData`]. Freshness of literals, provisional inference results,
//! overload picks, and narrowing all live in scoped side tables keyed by
//! occurrence/`NodeId` (see `pith-queries`), never in this shared interner.
//! Concretely: every field of [`TypeData`] must be a pure function of the
//! type's STRUCTURE. If a proposed field would vary between two occurrences of
//! the same shape (e.g. "is this literal fresh here?"), it is forbidden here.
//! The `freshness_is_not_representable` test pins this: interning one shape
//! twice yields one id, with no slot for per-occurrence state to hide in.
//!
//! Canonicalization: [`TypeStore::intern`] sorts object members by name and
//! sorts plus dedupes union variants, so structurally equal inputs hash equal
//! regardless of input order. Determinism: ids are assigned in first-intern
//! order, so a fixed input order always yields identical ids.

use std::collections::HashMap;

use pith_ids::TypeId;

/// Converts a `usize` store length into the next [`TypeId`].
///
/// Store lengths never approach address-space limits in practice; an
/// unrepresentable length saturates to [`TypeId::DUMMY`] instead of wrapping.
#[inline]
#[must_use]
fn next_id(len: usize) -> TypeId {
    TypeId(u32::try_from(len).unwrap_or(u32::MAX))
}

/// Converts a [`TypeId`] into a `usize` position for `Vec` lookup.
///
/// Indices originate as store positions; unrepresentable values saturate to
/// `usize::MAX` and therefore miss every bounds-checked lookup.
#[inline]
#[must_use]
fn idx(id: TypeId) -> usize {
    usize::try_from(id.0).unwrap_or(usize::MAX)
}

/// One structural type shape.
///
/// Pure structure only: see the module-level H-002 design law. There is
/// deliberately no freshness flag, no provisional-inference slot, no overload
/// pick, and no narrowing record anywhere in this enum.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeData {
    /// The bottom type: no value inhabits it.
    Never,
    /// An unresolved or erroneous type that must not poison the store.
    Unknown,
    /// The top type: any value is assignable to it.
    Any,
    /// The `number` primitive.
    Number,
    /// The `string` primitive.
    String,
    /// The `boolean` primitive.
    Boolean,
    /// The `void` primitive.
    Void,
    /// The `undefined` primitive.
    Undefined,
    /// The `null` primitive.
    Null,
    /// An object shape with members sorted by name (see [`TypeStore::intern`]).
    Object {
        /// `(member name, member type)` pairs, sorted by name, deduplicated.
        members: Vec<(String, TypeId)>,
    },
    /// A union of member types, sorted and deduplicated.
    Union(Vec<TypeId>),
}

/// Global hash-consed owner of [`TypeData`], keyed by [`TypeId`].
///
/// Built-in primitives occupy fixed ids `0..=8` in every store (see the
/// `NEVER`..=`NULL` constants), so cross-store snapshots agree on primitives.
#[derive(Clone, Debug)]
pub struct TypeStore {
    types: Vec<TypeData>,
    by_shape: HashMap<TypeData, TypeId>,
}

impl TypeStore {
    /// Primitive [`TypeData`] shapes in fixed-id order (`Never` first).
    const BUILTINS: [TypeData; 9] = [
        TypeData::Never,
        TypeData::Unknown,
        TypeData::Any,
        TypeData::Number,
        TypeData::String,
        TypeData::Boolean,
        TypeData::Void,
        TypeData::Undefined,
        TypeData::Null,
    ];

    /// [`TypeData::Never`], always id `0`.
    pub const NEVER: TypeId = TypeId(0);
    /// [`TypeData::Unknown`], always id `1`.
    pub const UNKNOWN: TypeId = TypeId(1);
    /// [`TypeData::Any`], always id `2`.
    pub const ANY: TypeId = TypeId(2);
    /// [`TypeData::Number`], always id `3`.
    pub const NUMBER: TypeId = TypeId(3);
    /// [`TypeData::String`], always id `4`.
    pub const STRING: TypeId = TypeId(4);
    /// [`TypeData::Boolean`], always id `5`.
    pub const BOOLEAN: TypeId = TypeId(5);
    /// [`TypeData::Void`], always id `6`.
    pub const VOID: TypeId = TypeId(6);
    /// [`TypeData::Undefined`], always id `7`.
    pub const UNDEFINED: TypeId = TypeId(7);
    /// [`TypeData::Null`], always id `8`.
    pub const NULL: TypeId = TypeId(8);

    /// A store pre-populated with the nine built-ins at their fixed ids.
    #[must_use]
    pub fn new() -> Self {
        let mut store = Self {
            types: Vec::with_capacity(Self::BUILTINS.len()),
            by_shape: HashMap::with_capacity(Self::BUILTINS.len()),
        };
        for shape in Self::BUILTINS.iter().cloned() {
            let id = next_id(store.types.len());
            store.types.push(shape.clone());
            store.by_shape.insert(shape, id);
        }
        store
    }

    /// Number of interned shapes, including the nine built-ins.
    #[must_use]
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Whether the store holds no shapes (never true for [`Self::new`]).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    /// Looks up the shape behind an id.
    #[must_use]
    pub fn get(&self, id: TypeId) -> Option<&TypeData> {
        self.types.get(idx(id))
    }

    /// Interns a shape, returning its canonical [`TypeId`].
    ///
    /// Canonicalization first: object members are sorted by name and
    /// deduplicated (first occurrence wins); union variants are sorted and
    /// deduplicated. Interning an equal shape twice returns the same id.
    /// Nested shapes are NOT flattened or rewritten (a single-variant union
    /// stays a union); that normalization belongs to a later phase.
    pub fn intern(&mut self, data: TypeData) -> TypeId {
        let shape = Self::canonicalize(data);
        if let Some(&id) = self.by_shape.get(&shape) {
            return id;
        }
        let id = next_id(self.types.len());
        self.types.push(shape.clone());
        self.by_shape.insert(shape, id);
        id
    }

    /// Iterates `(id, shape)` pairs in [`TypeId`] (insertion) order.
    pub fn iter(&self) -> impl Iterator<Item = (TypeId, &TypeData)> {
        self.types
            .iter()
            .enumerate()
            .map(|(index, shape)| (TypeId(u32::try_from(index).unwrap_or(u32::MAX)), shape))
    }

    /// Sorts object members / union variants into canonical order.
    fn canonicalize(data: TypeData) -> TypeData {
        match data {
            TypeData::Object { mut members } => {
                members.sort_by(|left, right| left.0.cmp(&right.0));
                members.dedup_by(|later, earlier| later.0 == earlier.0);
                TypeData::Object { members }
            }
            TypeData::Union(mut variants) => {
                variants.sort();
                variants.dedup();
                TypeData::Union(variants)
            }
            shape => shape,
        }
    }
}

impl Default for TypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn object(pairs: &[(&str, TypeId)]) -> TypeData {
        TypeData::Object {
            members: pairs
                .iter()
                .map(|(name, id)| ((*name).to_owned(), *id))
                .collect(),
        }
    }

    #[test]
    fn builtins_have_fixed_ids() {
        let store = TypeStore::new();
        let expected = [
            (TypeStore::NEVER, TypeData::Never),
            (TypeStore::UNKNOWN, TypeData::Unknown),
            (TypeStore::ANY, TypeData::Any),
            (TypeStore::NUMBER, TypeData::Number),
            (TypeStore::STRING, TypeData::String),
            (TypeStore::BOOLEAN, TypeData::Boolean),
            (TypeStore::VOID, TypeData::Void),
            (TypeStore::UNDEFINED, TypeData::Undefined),
            (TypeStore::NULL, TypeData::Null),
        ];
        assert_eq!(store.len(), expected.len());
        for (id, shape) in expected {
            assert_eq!(store.get(id), Some(&shape));
        }
        assert_eq!(TypeStore::NEVER, TypeId(0));
        assert_eq!(TypeStore::NULL, TypeId(8));
    }

    #[test]
    fn freshness_is_not_representable() {
        // H-002 guard: the same shape interned twice yields the same id.
        // There is no per-occurrence slot (freshness, provisional inference)
        // anywhere in TypeData for the two interns to differ by.
        let mut store = TypeStore::new();
        let first = store.intern(object(&[("a", TypeStore::NUMBER)]));
        let second = store.intern(object(&[("a", TypeStore::NUMBER)]));
        assert_eq!(first, second);
        assert_eq!(store.len(), 10);
    }

    #[test]
    fn distinct_structures_get_distinct_ids() {
        let mut store = TypeStore::new();
        let number_obj = store.intern(object(&[("a", TypeStore::NUMBER)]));
        let string_obj = store.intern(object(&[("a", TypeStore::STRING)]));
        let renamed = store.intern(object(&[("b", TypeStore::NUMBER)]));
        let union = store.intern(TypeData::Union(vec![TypeStore::NUMBER]));
        assert_ne!(number_obj, string_obj);
        assert_ne!(number_obj, renamed);
        assert_ne!(number_obj, union);
    }

    #[test]
    fn object_member_order_is_normalized() {
        let mut store = TypeStore::new();
        let forward = store.intern(object(&[
            ("a", TypeStore::NUMBER),
            ("b", TypeStore::STRING),
        ]));
        let backward = store.intern(object(&[
            ("b", TypeStore::STRING),
            ("a", TypeStore::NUMBER),
        ]));
        assert_eq!(forward, backward);
        let shape = store.get(forward).expect("interned");
        let TypeData::Object { members } = shape else {
            panic!("expected object shape, got {shape:?}");
        };
        let names: Vec<&str> = members.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["a", "b"]);
    }

    #[test]
    fn unions_are_sorted_and_deduped() {
        let mut store = TypeStore::new();
        let first = store.intern(TypeData::Union(vec![
            TypeStore::STRING,
            TypeStore::NUMBER,
            TypeStore::STRING,
        ]));
        let second = store.intern(TypeData::Union(vec![TypeStore::NUMBER, TypeStore::STRING]));
        assert_eq!(first, second);
        assert_eq!(
            store.get(first),
            Some(&TypeData::Union(vec![TypeStore::NUMBER, TypeStore::STRING]))
        );
    }

    #[test]
    fn interning_is_deterministic_for_fixed_input_order() {
        let shapes = [
            object(&[("x", TypeStore::NUMBER)]),
            TypeData::Union(vec![TypeStore::STRING, TypeStore::BOOLEAN]),
            object(&[]),
        ];
        let mut first = TypeStore::new();
        let first_ids: Vec<TypeId> = shapes.iter().cloned().map(|s| first.intern(s)).collect();
        let mut second = TypeStore::new();
        let second_ids: Vec<TypeId> = shapes.iter().cloned().map(|s| second.intern(s)).collect();
        assert_eq!(first_ids, second_ids);
    }
}
