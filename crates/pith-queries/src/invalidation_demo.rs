//! PITH-P007 invalidation demo: a 50-file synthetic project through [`QueryDb`].
//!
//! Model: file 0 is the shared types file; files 1..=49 form an import chain
//! where file `i` records its transitive import closure (`0..=i`) as query
//! deps. Each file owns one node ([`FILE_NODE`]), its exported-type query.
//! The surgical edit flips one member type in file 25, so the affected set is
//! files 25..=49: a strict subset of the 50-file project.
//!
//! Counts asserted (not timed): cold pass 50 recomputes, clean re-pass 50
//! hits, `invalidate` drops 25 entries, post-edit re-pass 25 recomputes.
//! Post-edit answers must equal a from-scratch cold rebuild structurally:
//! [`TypeId`](pith_ids::TypeId)s are store-relative insertion order, so the
//! gate compares fully resolved shapes, not raw ids.

use pith_ids::{FileId, NodeId, TypeId};
use pith_types::{TypeData, TypeStore};

use super::{Dep, QueryDb, QueryKey, QueryKind};

/// Simulated files: shared (0) plus a 49-file import chain.
const FILE_COUNT: u32 = 50;
/// File receiving the surgical edit; files `EDIT_FILE..` are affected.
const EDIT_FILE: u32 = 25;
/// The single node owned by every simulated file.
const FILE_NODE: u32 = 0;

/// Zero-padded value-member name for `file` (`v01`..`v49`).
#[must_use]
fn value_member(file: u32) -> String {
    format!("v{file:02}")
}

/// Key for a file's exported-type query.
#[must_use]
fn file_key(file: u32) -> QueryKey {
    QueryKey {
        file: FileId(file),
        node: NodeId(FILE_NODE),
        kind: QueryKind::TypeOf,
    }
}

/// Dependency edge on a file's node.
#[must_use]
fn file_dep(file: u32) -> Dep {
    Dep {
        file: FileId(file),
        node: NodeId(FILE_NODE),
    }
}

/// Transitive import closure of `file`: itself plus every upstream file.
///
/// Recording the full closure is what lets the single-hop
/// [`QueryDb::invalidate`] drop exactly the downstream cone of an edit.
#[must_use]
fn closure_deps(file: u32) -> Vec<Dep> {
    (0u32..=file).map(file_dep).collect()
}

/// Structural shape of `file` given its predecessor's answer.
///
/// File 0 (`shared`) is `{ id: number, name: string }`; chain file `i` is
/// `{ prev, tag, vNN }` where `prev` is the upstream answer. With `edited`,
/// file [`EDIT_FILE`] flips its value member `number` -> `string`: the one
/// surgical edit, cascading downstream through `prev`.
#[must_use]
fn shape_for(file: u32, prev: TypeId, edited: bool) -> TypeData {
    if file == 0 {
        return TypeData::Object {
            members: vec![
                ("id".to_owned(), TypeStore::NUMBER),
                ("name".to_owned(), TypeStore::STRING),
            ],
        };
    }
    let value = if edited && file == EDIT_FILE {
        TypeStore::STRING
    } else {
        TypeStore::NUMBER
    };
    TypeData::Object {
        members: vec![
            ("prev".to_owned(), prev),
            ("tag".to_owned(), TypeStore::STRING),
            (value_member(file), value),
        ],
    }
}

/// One full query pass over all files in file order (deterministic ids).
///
/// With `recompute`, each file interns its current shape then memoizes it;
/// otherwise a poison fallback proves hits: any miss would return
/// [`TypeStore::NULL`] and fail the caller's equality check.
fn query_pass(db: &mut QueryDb, edited: bool, recompute: bool) -> Vec<TypeId> {
    let mut answers = Vec::new();
    for file in 0u32..FILE_COUNT {
        let prev = answers.last().copied().unwrap_or(TypeStore::NULL);
        let key = file_key(file);
        let deps = closure_deps(file);
        let answer = if recompute {
            let id = db.types_mut().intern(shape_for(file, prev, edited));
            db.type_of(key, &deps, || id)
        } else {
            db.type_of(key, &deps, || TypeStore::NULL)
        };
        answers.push(answer);
    }
    answers
}

/// Renders one interned shape with nested ids fully resolved.
///
/// Recursion terminates on this fixture: every `prev` edge points strictly
/// upstream and file 0 has no `prev`.
#[must_use]
fn render(store: &TypeStore, id: TypeId) -> String {
    match store.get(id) {
        Some(TypeData::Object { members }) => {
            let parts: Vec<String> = members
                .iter()
                .map(|(name, member)| format!("{name}:{}", render(store, *member)))
                .collect();
            format!("{{{}}}", parts.join(","))
        }
        Some(TypeData::Union(variants)) => {
            let parts: Vec<String> = variants
                .iter()
                .map(|variant| render(store, *variant))
                .collect();
            format!("({})", parts.join("|"))
        }
        Some(TypeData::Never) => "never".to_owned(),
        Some(TypeData::Unknown) => "unknown".to_owned(),
        Some(TypeData::Any) => "any".to_owned(),
        Some(TypeData::Number) => "number".to_owned(),
        Some(TypeData::String) => "string".to_owned(),
        Some(TypeData::Boolean) => "boolean".to_owned(),
        Some(TypeData::Void) => "void".to_owned(),
        Some(TypeData::Undefined) => "undefined".to_owned(),
        Some(TypeData::Null) => "null".to_owned(),
        None => "dangling".to_owned(),
    }
}

#[test]
fn fifty_file_chain_invalidates_only_downstream() {
    // Cold pass: every file misses exactly once.
    let mut db = QueryDb::new();
    let cold = query_pass(&mut db, false, true);
    assert_eq!(db.recompute_count(), u64::from(FILE_COUNT));
    assert_eq!(db.cache_len(), cold.len());

    // Clean re-pass: the poison fallback proves all 50 queries hit.
    let clean = query_pass(&mut db, false, false);
    assert_eq!(clean, cold);
    assert_eq!(db.recompute_count(), u64::from(FILE_COUNT));

    // Surgical edit on file 25: invalidate its node, then check the
    // surviving cache is exactly the untouched upstream files.
    let dropped = db.invalidate(file_dep(EDIT_FILE));
    let mut untouched = 0usize;
    for file in 0u32..FILE_COUNT {
        if db.cached_deps(&file_key(file)).is_some() {
            untouched += 1;
            assert!(file < EDIT_FILE, "only upstream files survive");
        } else {
            assert!(file >= EDIT_FILE, "affected file {file} is dropped");
        }
    }
    assert_eq!(dropped, cold.len() - untouched);
    assert_eq!(dropped, untouched, "mid-chain edit splits the project");
    assert!(dropped < cold.len(), "invalidation is a strict subset");

    // Post-edit re-pass: only the affected cone recomputes; upstream
    // answers are byte-identical hits, and the edit lands at index 25.
    let before = db.recompute_count();
    let post = query_pass(&mut db, true, true);
    let delta = db.recompute_count() - before;
    assert_eq!(delta, u64::try_from(dropped).expect("fits in u64"));
    assert_eq!(post[..untouched], cold[..untouched]);
    assert_ne!(post[untouched], cold[untouched]);
    assert_eq!(db.cache_len(), cold.len());
    assert_eq!(
        db.recompute_count(),
        u64::from(FILE_COUNT).saturating_add(delta)
    );

    // Equivalence gate: a from-scratch cold rebuild with the edit applied
    // resolves to identical structure for every file.
    let mut fresh = QueryDb::new();
    let rebuilt = query_pass(&mut fresh, true, true);
    assert_eq!(fresh.recompute_count(), u64::from(FILE_COUNT));
    for (index, (post_id, rebuilt_id)) in post.iter().zip(rebuilt.iter()).enumerate() {
        assert_eq!(
            render(db.types(), *post_id),
            render(fresh.types(), *rebuilt_id),
            "file at pass index {index} matches a cold rebuild"
        );
    }
}
