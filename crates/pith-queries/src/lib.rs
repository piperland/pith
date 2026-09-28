//! Pith memoized semantic queries: [`QueryDb`] + [`QueryKey`].
//!
//! Queries memoize per `(file, node, kind)` key and record explicit
//! dependency edges ([`Dep`]) so a later edit can invalidate exactly the
//! cached entries that (transitively, once a solver walks edges) depend on a
//! changed node. A cache hit never recomputes; [`QueryDb::recompute_count`]
//! makes hits and misses observable in tests.
//!
//! Design law (H-002): occurrence-varying state (freshness, provisional
//! inference, overload picks) lives in side tables keyed by occurrence — here
//! that means per-[`QueryKey`] cache entries — and never in [`TypeData`].
//! The shared [`TypeStore`] holds structure only; this crate holds verdicts.
//!
//! Name resolution seam: [`QueryDb`] owns a [`Binder`] so future phases
//! (P007) can thread [`SymbolId`] lookups through queries without
//! restructuring the database. [`QueryDb::resolve`] is the documented stub
//! for that integration and is covered by `resolve_delegates_to_binder`.

use std::collections::{BTreeMap, HashMap};

use pith_ids::{FileId, NodeId, SymbolId, TypeId};
use pith_symbols::Binder;
use pith_types::{TypeData, TypeStore};

#[cfg(test)]
mod invalidation_demo;

/// Which question a [`QueryKey`] asks. Extend with new variants as the
/// solver grows (each new kind gets its own memo namespace for free, since
/// the kind is part of the key).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum QueryKind {
    /// The type of the node itself.
    TypeOf,
    /// The member list of the node's type (objects; unions merge members).
    MembersOf,
}

/// A memoized query identity: one question about one node in one file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct QueryKey {
    /// File owning the queried node.
    pub file: FileId,
    /// Queried node.
    pub node: NodeId,
    /// Question being asked.
    pub kind: QueryKind,
}

/// A dependency edge: the query result was computed from this node.
///
/// [`QueryDb::invalidate`] drops every cached entry whose recorded edges
/// contain the invalidated node.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Dep {
    /// File owning the depended-on node.
    pub file: FileId,
    /// Depended-on node.
    pub node: NodeId,
}

/// Memoized semantic query database over one [`TypeStore`].
///
/// Owns the interner (`types`), the name-resolution side table (`binder`),
/// the memo cache, and a recompute counter for hit/miss observability.
#[derive(Clone, Debug, Default)]
pub struct QueryDb {
    types: TypeStore,
    binder: Binder,
    recompute_count: u64,
    cache: HashMap<QueryKey, (TypeId, Vec<Dep>)>,
}

impl QueryDb {
    /// An empty database with fresh built-in types and no cached queries.
    #[must_use]
    pub fn new() -> Self {
        Self {
            types: TypeStore::new(),
            binder: Binder::new(),
            recompute_count: 0,
            cache: HashMap::new(),
        }
    }

    /// The shared structural interner (structure only, never verdicts).
    #[must_use]
    pub fn types(&self) -> &TypeStore {
        &self.types
    }

    /// Mutable access to the interner for `intern`ing new shapes.
    pub fn types_mut(&mut self) -> &mut TypeStore {
        &mut self.types
    }

    /// The name-resolution side table (the P007 resolve seam).
    #[must_use]
    pub fn binder(&self) -> &Binder {
        &self.binder
    }

    /// Mutable access to the binder for `build_file` ingestion.
    pub fn binder_mut(&mut self) -> &mut Binder {
        &mut self.binder
    }

    /// Number of cache misses (real recomputes) served so far.
    ///
    /// Cache hits never touch this counter; tests use it to observe memo
    /// behavior without timing.
    #[must_use]
    pub fn recompute_count(&self) -> u64 {
        self.recompute_count
    }

    /// Number of currently cached query entries.
    #[must_use]
    pub fn cache_len(&self) -> usize {
        self.cache.len()
    }

    /// Dependency edges recorded for a cached query, if present.
    #[must_use]
    pub fn cached_deps(&self, key: &QueryKey) -> Option<&[Dep]> {
        self.cache.get(key).map(|(_, deps)| deps.as_slice())
    }

    /// Resolves `name` from `scope` in `file` via the owned [`Binder`].
    ///
    /// Documented stub seam for P007: the future solver will call this while
    /// computing [`QueryKind::TypeOf`] answers so name lookups flow through
    /// the same database (and its invalidation) as type queries. Today it
    /// delegates directly; returns `None` for unknown names, mirroring
    /// [`Binder::resolve`].
    #[must_use]
    pub fn resolve(&self, file: FileId, scope: u32, name: &str) -> Option<SymbolId> {
        self.binder.resolve(file, scope, name)
    }

    /// Answers `key` with [`QueryKind::TypeOf`], memoizing the result.
    ///
    /// On a cache hit `compute` is not called and [`Self::recompute_count`]
    /// is unchanged. On a miss `compute` runs once, the counter increments
    /// by one, and `deps` (sorted, deduplicated) are recorded with the entry.
    /// Callers must pass `key` with `kind` [`QueryKind::TypeOf`]; the kind is
    /// stored as given and namespaces the memo entry.
    #[must_use]
    pub fn type_of(
        &mut self,
        key: QueryKey,
        deps: &[Dep],
        compute: impl FnOnce() -> TypeId,
    ) -> TypeId {
        self.query(key, deps, compute)
    }

    /// Answers `key` with [`QueryKind::MembersOf`], memoizing the result.
    ///
    /// Memoization behaves exactly like [`Self::type_of`]; the returned
    /// member list is then resolved structurally from the memoized type:
    /// objects yield their (sorted) members, unions yield the merged members
    /// of their variants (first variant in sorted-[`TypeId`] order wins on
    /// name conflicts), and every other shape yields an empty list.
    #[must_use]
    pub fn members_of(
        &mut self,
        key: QueryKey,
        deps: &[Dep],
        compute: impl FnOnce() -> TypeId,
    ) -> Vec<(String, TypeId)> {
        let id = self.query(key, deps, compute);
        self.resolve_members(id)
    }

    /// Drops every cached entry whose recorded edges contain `dep`.
    ///
    /// Returns the number of entries dropped, so callers (and tests) can
    /// observe invalidation precision. Entries not depending on `dep` are
    /// untouched.
    pub fn invalidate(&mut self, dep: Dep) -> usize {
        let before = self.cache.len();
        self.cache.retain(|_, (_, deps)| !deps.contains(&dep));
        before.saturating_sub(self.cache.len())
    }

    /// Core memo wrapper shared by [`Self::type_of`] and [`Self::members_of`].
    fn query(&mut self, key: QueryKey, deps: &[Dep], compute: impl FnOnce() -> TypeId) -> TypeId {
        if let Some((value, _)) = self.cache.get(&key) {
            return *value;
        }
        let value = compute();
        self.recompute_count = self.recompute_count.saturating_add(1);
        let mut owned: Vec<Dep> = deps.to_vec();
        owned.sort();
        owned.dedup();
        self.cache.insert(key, (value, owned));
        value
    }

    /// Resolves the member list of one interned shape (pure structure read).
    fn resolve_members(&self, id: TypeId) -> Vec<(String, TypeId)> {
        match self.types.get(id) {
            Some(TypeData::Object { members }) => members.clone(),
            Some(TypeData::Union(variants)) => {
                let mut merged = BTreeMap::new();
                for variant in variants {
                    if let Some(TypeData::Object { members }) = self.types.get(*variant) {
                        for (name, member) in members {
                            merged.entry(name.clone()).or_insert(*member);
                        }
                    }
                }
                merged.into_iter().collect()
            }
            Some(_) | None => Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pith_symbols::{ScopeInput, SymbolInput};
    use pith_types::TypeData;

    const FILE: FileId = FileId(0);

    fn key(node: u32, kind: QueryKind) -> QueryKey {
        QueryKey {
            file: FILE,
            node: NodeId(node),
            kind,
        }
    }

    fn dep(node: u32) -> Dep {
        Dep {
            file: FILE,
            node: NodeId(node),
        }
    }

    #[test]
    fn memo_hit_skips_recompute() {
        let mut db = QueryDb::new();
        let expected = TypeStore::NUMBER;
        let first = db.type_of(key(1, QueryKind::TypeOf), &[dep(7)], || expected);
        assert_eq!(first, expected);
        assert_eq!(db.recompute_count(), 1);
        let second = db.type_of(key(1, QueryKind::TypeOf), &[dep(7)], || TypeStore::STRING);
        assert_eq!(second, expected);
        assert_eq!(db.recompute_count(), 1);
        assert_eq!(db.cache_len(), 1);
    }

    #[test]
    fn deps_are_recorded_per_query() {
        let mut db = QueryDb::new();
        let _ = db.type_of(key(1, QueryKind::TypeOf), &[dep(8), dep(7)], || {
            TypeStore::NUMBER
        });
        assert_eq!(
            db.cached_deps(&key(1, QueryKind::TypeOf)),
            Some(&[dep(7), dep(8)][..])
        );
        assert_eq!(db.cached_deps(&key(2, QueryKind::TypeOf)), None);
    }

    #[test]
    fn invalidate_drops_only_affected_entries() {
        let mut db = QueryDb::new();
        let _ = db.type_of(key(1, QueryKind::TypeOf), &[dep(7)], || TypeStore::NUMBER);
        let _ = db.type_of(key(2, QueryKind::TypeOf), &[dep(9)], || TypeStore::STRING);
        assert_eq!(db.cache_len(), 2);
        assert_eq!(db.invalidate(dep(7)), 1);
        assert_eq!(db.cache_len(), 1);
        assert_eq!(
            db.cached_deps(&key(2, QueryKind::TypeOf)),
            Some(&[dep(9)][..])
        );
        let _ = db.type_of(key(1, QueryKind::TypeOf), &[dep(7)], || TypeStore::BOOLEAN);
        assert_eq!(db.recompute_count(), 3);
        let untouched = db.type_of(key(2, QueryKind::TypeOf), &[], || TypeStore::BOOLEAN);
        assert_eq!(untouched, TypeStore::STRING);
        assert_eq!(db.recompute_count(), 3);
    }

    #[test]
    fn union_members_merge_across_variants() {
        let mut db = QueryDb::new();
        let left = db.types_mut().intern(TypeData::Object {
            members: vec![
                ("a".to_owned(), TypeStore::NUMBER),
                ("shared".to_owned(), TypeStore::NUMBER),
            ],
        });
        let right = db.types_mut().intern(TypeData::Object {
            members: vec![
                ("b".to_owned(), TypeStore::STRING),
                ("shared".to_owned(), TypeStore::STRING),
            ],
        });
        let union = db.types_mut().intern(TypeData::Union(vec![left, right]));
        let members = db.members_of(key(4, QueryKind::MembersOf), &[dep(4)], || union);
        let names: Vec<&str> = members.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["a", "b", "shared"]);
        assert_eq!(
            db.members_of(key(5, QueryKind::MembersOf), &[], || TypeStore::NUMBER),
            []
        );
    }

    #[test]
    fn members_of_memoizes_like_type_of() {
        let mut db = QueryDb::new();
        let object = db.types_mut().intern(TypeData::Object {
            members: vec![("a".to_owned(), TypeStore::NUMBER)],
        });
        let first = db.members_of(key(6, QueryKind::MembersOf), &[dep(6)], || object);
        assert_eq!(first.len(), 1);
        assert_eq!(db.recompute_count(), 1);
        let second = db.members_of(key(6, QueryKind::MembersOf), &[], || TypeStore::NULL);
        assert_eq!(second, first);
        assert_eq!(db.recompute_count(), 1);
    }

    #[test]
    fn resolve_delegates_to_binder() {
        let mut db = QueryDb::new();
        let span = pith_ids::Span {
            file: FILE,
            lo: 0,
            hi: 1,
        };
        db.binder_mut().build_file(
            FILE,
            &[ScopeInput {
                index: 0,
                parent: u32::MAX,
            }],
            &[SymbolInput {
                scope: 0,
                name: "x".to_owned(),
                span,
                flags: 0,
            }],
            &[],
        );
        assert!(db.resolve(FILE, 0, "x").is_some());
        assert_eq!(db.resolve(FILE, 0, "missing"), None);
    }
}
