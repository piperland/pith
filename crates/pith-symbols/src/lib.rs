//! Pith symbol tables: [`SymbolStore`] + [`Binder`].
//!
//! The binder consumes Pith-owned frontend facts (scope parents, symbol
//! declarations, unresolved names) and produces stable [`SymbolId`] identities
//! with one lexical scope tree per file.
//!
//! Boundary law: this crate depends only on `pith-ids` (plus `std`). It never
//! imports `pith-frontend` or any `oxc_*` crate. The plain [`ScopeInput`] /
//! [`SymbolInput`] / [`UnresolvedInput`] structs are the only ingestion shape;
//! test code adapts `pith_frontend::ParsedFile` into them (see `tests`).
//!
//! Design law (H-002): occurrence-varying state stays out of interned tables.
//! The store records declarations only. Reference counts and reference names
//! carried by frontend facts are deliberately dropped here; per-occurrence
//! data belongs in later side tables keyed by occurrence id. Likewise,
//! [`UnresolvedRef`] entries live in the [`Binder`], never as symbols.
//!
//! Determinism: [`SymbolStore`] iterates in [`SymbolId`] insertion order, which
//! is fixed whenever the input fact order is fixed (the frontend already emits
//! scopes root-first, symbols in id order, and unresolved names sorted).
//! Per-scope bindings iterate in name order; unresolved refs are stored sorted
//! by name. Rebuilding the same facts into a fresh [`Binder`] therefore yields
//! identical iteration order.
//!
//! Cross-file module resolution lives in [`multifile`]: specifiers to
//! [`FileId`]s, imports to declaring files, over driver-adapted module facts.
//!
//! Scope-index convention: per-file scope indices come from the frontend with
//! the root at 0. A parent of `u32::MAX` means "no parent" (the root).

use std::collections::{BTreeMap, HashMap};

use pith_ids::{FileId, Span, SymbolId};

/// Cross-file module resolution (specifiers to files, imports to declarations).
pub mod multifile;

/// Converts a `u32` per-file index into a `usize` position for `Vec` lookup.
///
/// Indices originate as per-file counters that never approach address-space
/// limits; unrepresentable values saturate to `usize::MAX` and therefore miss
/// every bounds-checked lookup instead of wrapping.
#[inline]
#[must_use]
fn idx(v: u32) -> usize {
    usize::try_from(v).unwrap_or(usize::MAX)
}

/// A scope address: owning file plus the frontend's per-file scope index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ScopeKey {
    /// File that owns the scope tree.
    pub file: FileId,
    /// Per-file scope index (root is 0).
    pub index: u32,
}

/// One interned symbol: every merged TypeScript declaration sharing a single
/// name-plus-scope identity.
///
/// `file`/`span` describe the first observed declaration; the full set lives
/// in `declarations`. `flags` is the bitwise OR of the opaque frontend flag
/// bits across merged declarations.
#[derive(Clone, Debug)]
pub struct Symbol {
    /// Declared name.
    pub name: String,
    /// File of the first declaration.
    pub file: FileId,
    /// Span of the first declaration.
    pub span: Span,
    /// Scope that owns this name.
    pub scope: ScopeKey,
    /// Every merged declaration, first declaration first.
    pub declarations: Vec<(FileId, Span)>,
    /// Opaque frontend flag bits, OR-ed across merged declarations.
    pub flags: u32,
}

/// Vec-backed interner-style owner of [`Symbol`]s, keyed by [`SymbolId`].
#[derive(Clone, Debug, Default)]
pub struct SymbolStore {
    symbols: Vec<Symbol>,
    by_key: HashMap<(FileId, u32, String), SymbolId>,
}

impl SymbolStore {
    /// An empty store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            symbols: Vec::new(),
            by_key: HashMap::new(),
        }
    }

    /// Number of interned symbols.
    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Whether the store holds no symbols.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Looks up a symbol by id.
    #[must_use]
    pub fn get(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(idx(id.0))
    }

    /// Looks up the merged symbol for one name in one file scope.
    #[must_use]
    pub fn lookup(&self, file: FileId, scope: u32, name: &str) -> Option<SymbolId> {
        self.by_key.get(&(file, scope, name.to_owned())).copied()
    }

    /// Interns a declaration, merging with the existing symbol when the same
    /// name was already declared in the same file scope.
    ///
    /// Merging rule: same `(file, scope, name)` always merges into one
    /// [`SymbolId`]; the new `(file, span)` is appended to `declarations` and
    /// `flags` are OR-ed. Rationale: TypeScript lets one name carry several
    /// meanings at once (interface + value, namespace augmentation,
    /// overloads), while the flag bits are opaque at this layer so
    /// kind-compatibility cannot be judged here. Genuine conflicts surface via
    /// frontend diagnostics and later type checking, not identity.
    pub fn declare(
        &mut self,
        name: &str,
        file: FileId,
        span: Span,
        scope: ScopeKey,
        flags: u32,
    ) -> SymbolId {
        let key = (file, scope.index, name.to_owned());
        if let Some(&id) = self.by_key.get(&key) {
            if let Some(symbol) = self.symbols.get_mut(idx(id.0)) {
                symbol.declarations.push((file, span));
                symbol.flags |= flags;
            }
            return id;
        }
        let id = SymbolId(u32::try_from(self.symbols.len()).unwrap_or(u32::MAX));
        self.symbols.push(Symbol {
            name: name.to_owned(),
            file,
            span,
            scope,
            declarations: vec![(file, span)],
            flags,
        });
        self.by_key.insert(key, id);
        id
    }

    /// Iterates symbols in [`SymbolId`] (insertion) order.
    pub fn iter(&self) -> std::slice::Iter<'_, Symbol> {
        self.symbols.iter()
    }

    /// Collects `(id, symbol)` pairs sorted by name, then id.
    ///
    /// Deterministic regardless of declaration order; useful for snapshots and
    /// tests. The store itself always iterates in insertion order.
    #[must_use]
    pub fn iter_sorted_by_name(&self) -> Vec<(SymbolId, &Symbol)> {
        let mut out: Vec<(SymbolId, &Symbol)> = self
            .symbols
            .iter()
            .enumerate()
            .map(|(i, symbol)| (SymbolId(u32::try_from(i).unwrap_or(u32::MAX)), symbol))
            .collect();
        out.sort_by(|a, b| a.1.name.cmp(&b.1.name).then(a.0.cmp(&b.0)));
        out
    }
}

impl<'a> IntoIterator for &'a SymbolStore {
    type Item = &'a Symbol;
    type IntoIter = std::slice::Iter<'a, Symbol>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// One frontend scope: parent link plus the names bound directly in it.
#[derive(Clone, Debug, Default)]
pub struct ScopeNode {
    parent: Option<u32>,
    bindings: BTreeMap<String, SymbolId>,
}

impl ScopeNode {
    /// Parent per-file scope index, or `None` for the file root.
    #[must_use]
    pub fn parent(&self) -> Option<u32> {
        self.parent
    }

    /// The symbol bound directly in this scope under `name`, if any.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<SymbolId> {
        self.bindings.get(name).copied()
    }

    /// Direct bindings in name order.
    #[must_use]
    pub fn bindings(&self) -> &BTreeMap<String, SymbolId> {
        &self.bindings
    }
}

/// One frontend scope fact, adapted into binder input.
#[derive(Clone, Debug)]
pub struct ScopeInput {
    /// Per-file scope index.
    pub index: u32,
    /// Parent per-file scope index, or `u32::MAX` for the root.
    pub parent: u32,
}

/// One frontend symbol fact, adapted into binder input.
///
/// Occurrence state (`resolved_ref_count`, resolved reference names) is
/// intentionally absent: per H-002 it must never enter interned tables.
#[derive(Clone, Debug)]
pub struct SymbolInput {
    /// Owning per-file scope index.
    pub scope: u32,
    /// Declared name.
    pub name: String,
    /// Declaration span.
    pub span: Span,
    /// Opaque frontend flag bits.
    pub flags: u32,
}

/// One frontend unresolved-name fact, adapted into binder input.
#[derive(Clone, Debug)]
pub struct UnresolvedInput {
    /// Unresolved name.
    pub name: String,
    /// Occurrence count.
    pub count: u32,
}

/// An unresolved (global or undeclared) reference recorded by the binder.
///
/// Kept as a side-table entry on the [`Binder`], never interned as a symbol.
#[derive(Clone, Debug)]
pub struct UnresolvedRef {
    /// Unresolved name.
    pub name: String,
    /// File the reference occurs in.
    pub file: FileId,
    /// Occurrence count reported by the frontend.
    pub count: u32,
}

/// Owns the [`SymbolStore`], one scope tree per file, and unresolved refs.
#[derive(Clone, Debug, Default)]
pub struct Binder {
    store: SymbolStore,
    trees: HashMap<FileId, Vec<ScopeNode>>,
    unresolved: Vec<UnresolvedRef>,
}

impl Binder {
    /// An empty binder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            store: SymbolStore::new(),
            trees: HashMap::new(),
            unresolved: Vec::new(),
        }
    }

    /// The owned symbol store.
    #[must_use]
    pub fn store(&self) -> &SymbolStore {
        &self.store
    }

    /// The scope tree for `file`, indexed by per-file scope index.
    #[must_use]
    pub fn scopes_of(&self, file: FileId) -> Option<&[ScopeNode]> {
        self.trees.get(&file).map(Vec::as_slice)
    }

    /// Number of scope nodes built for `file` (0 when the file is unknown).
    #[must_use]
    pub fn scope_count(&self, file: FileId) -> usize {
        self.trees.get(&file).map_or(0, Vec::len)
    }

    /// All unresolved refs, sorted by file then name.
    #[must_use]
    pub fn unresolved(&self) -> &[UnresolvedRef] {
        &self.unresolved
    }

    /// Binds one file's facts into the store and records its scope tree.
    ///
    /// Symbols are declared in input order, so [`SymbolId`] assignment is
    /// deterministic for deterministic input. A symbol whose scope index is
    /// unknown to the tree falls back to the file root (index 0), as does
    /// [`resolve`](Self::resolve) from an unknown scope, keeping the two
    /// symmetric under frontend skew. Rebuilding the same file replaces its
    /// scope tree and unresolved entries; store interning itself is additive
    /// (fine-grained invalidation belongs to a later phase).
    pub fn build_file(
        &mut self,
        file: FileId,
        scopes: &[ScopeInput],
        symbols: &[SymbolInput],
        unresolved: &[UnresolvedInput],
    ) {
        let mut ordered: Vec<&ScopeInput> = scopes.iter().collect();
        ordered.sort_by_key(|scope| scope.index);
        let width = ordered
            .last()
            .map_or(1, |scope| idx(scope.index).saturating_add(1));
        let mut nodes: Vec<ScopeNode> = vec![ScopeNode::default(); width];
        for scope in ordered {
            if let Some(node) = nodes.get_mut(idx(scope.index)) {
                node.parent = if scope.parent == u32::MAX {
                    None
                } else {
                    Some(scope.parent)
                };
            }
        }

        for symbol in symbols {
            let key = ScopeKey {
                file,
                index: symbol.scope,
            };
            let id = self
                .store
                .declare(&symbol.name, file, symbol.span, key, symbol.flags);
            let at = idx(symbol.scope);
            if let Some(node) = nodes.get_mut(at) {
                node.bindings.insert(symbol.name.clone(), id);
            } else if let Some(root) = nodes.first_mut() {
                root.bindings.insert(symbol.name.clone(), id);
            }
        }
        self.trees.insert(file, nodes);

        let mut refs: Vec<UnresolvedRef> = unresolved
            .iter()
            .map(|fact| UnresolvedRef {
                name: fact.name.clone(),
                file,
                count: fact.count,
            })
            .collect();
        refs.sort_by(|a, b| a.name.cmp(&b.name));
        self.unresolved.retain(|kept| kept.file != file);
        self.unresolved.extend(refs);
        self.unresolved
            .sort_by(|a, b| (a.file, &a.name).cmp(&(b.file, &b.name)));
    }

    /// Resolves `name` from `scope` in `file`, walking up scope parents.
    ///
    /// Returns `None` for unknown files, unknown names, and unresolved
    /// globals (which are recorded as [`UnresolvedRef`], never as symbols). A
    /// start scope unknown to the tree falls back to the file root.
    #[must_use]
    pub fn resolve(&self, file: FileId, scope: u32, name: &str) -> Option<SymbolId> {
        let nodes = self.trees.get(&file)?;
        let mut current = if nodes.get(idx(scope)).is_some() {
            Some(scope)
        } else {
            Some(0)
        };
        while let Some(index) = current {
            let node = nodes.get(idx(index))?;
            if let Some(&id) = node.bindings.get(name) {
                return Some(id);
            }
            current = node.parent;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pith_frontend::{parse_module, ParsedFile};

    fn build_parsed(binder: &mut Binder, parsed: &ParsedFile) {
        let scopes: Vec<ScopeInput> = parsed
            .scopes
            .iter()
            .map(|scope| ScopeInput {
                index: scope.index,
                parent: scope.parent,
            })
            .collect();
        let symbols: Vec<SymbolInput> = parsed
            .symbols
            .iter()
            .map(|symbol| SymbolInput {
                scope: symbol.scope,
                name: symbol.name.clone(),
                span: symbol.span,
                flags: symbol.flags,
            })
            .collect();
        let unresolved: Vec<UnresolvedInput> = parsed
            .unresolved
            .iter()
            .map(|fact| UnresolvedInput {
                name: fact.name.clone(),
                count: fact.count,
            })
            .collect();
        binder.build_file(parsed.file, &scopes, &symbols, &unresolved);
    }

    fn scope_of(parsed: &ParsedFile, name: &str) -> u32 {
        parsed
            .symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .unwrap_or_else(|| panic!("expected symbol {name}"))
            .scope
    }

    const SAMPLE: &str = concat!(
        "import { b } from \"./b\";\n",
        "const x: number = 1;\n",
        "export function f(a: string): string { return a + b; }\n",
    );

    #[test]
    fn resolves_adapter_sample_names() {
        let parsed = parse_module(FileId(0), "a.ts", SAMPLE);
        assert!(parsed.errors.is_empty(), "errors: {:?}", parsed.errors);
        let mut binder = Binder::new();
        build_parsed(&mut binder, &parsed);

        let file = FileId(0);
        for name in ["x", "f", "b"] {
            let id = binder
                .resolve(file, scope_of(&parsed, name), name)
                .unwrap_or_else(|| panic!("expected {name} to resolve"));
            assert_eq!(binder.store().get(id).expect("interned").name, name);
        }
        let x = binder.resolve(file, scope_of(&parsed, "x"), "x");
        let f = binder.resolve(file, scope_of(&parsed, "f"), "f");
        assert_ne!(x, f);
    }

    #[test]
    fn merges_interface_plus_value() {
        let parsed = parse_module(
            FileId(1),
            "m.ts",
            "interface Foo { a: string; }\nconst Foo = 42;\n",
        );
        let mut binder = Binder::new();
        build_parsed(&mut binder, &parsed);

        let file = FileId(1);
        let facts: Vec<_> = parsed
            .symbols
            .iter()
            .filter(|symbol| symbol.name == "Foo")
            .collect();
        assert!(!facts.is_empty(), "expected at least one Foo fact");
        let id = binder
            .resolve(file, facts[0].scope, "Foo")
            .expect("Foo resolves");
        for fact in &facts[1..] {
            assert_eq!(binder.resolve(file, fact.scope, "Foo"), Some(id));
        }
        let symbol = binder.store().get(id).expect("interned");
        assert_eq!(symbol.declarations.len(), facts.len());
        assert_eq!(
            symbol.flags,
            facts.iter().fold(0, |acc, fact| acc | fact.flags)
        );
        let foos: Vec<_> = binder
            .store()
            .iter()
            .filter(|symbol| symbol.name == "Foo")
            .collect();
        assert_eq!(foos.len(), 1);
    }

    #[test]
    fn unresolved_names_are_not_symbols() {
        let parsed = parse_module(FileId(2), "g.ts", "console.log(missing);\n");
        let mut binder = Binder::new();
        build_parsed(&mut binder, &parsed);

        let file = FileId(2);
        let names: Vec<&str> = binder
            .unresolved()
            .iter()
            .filter(|entry| entry.file == file)
            .map(|entry| entry.name.as_str())
            .collect();
        assert!(names.contains(&"console"), "unresolved: {names:?}");
        assert!(names.contains(&"missing"), "unresolved: {names:?}");
        assert!(binder.scope_count(file) > 0);
        assert_eq!(binder.resolve(file, 0, "console"), None);
        assert_eq!(binder.resolve(file, 0, "missing"), None);
        assert!(binder.store().lookup(file, 0, "console").is_none());
        assert!(binder.store().lookup(file, 0, "missing").is_none());
    }

    #[test]
    fn build_is_deterministic() {
        let parsed = parse_module(FileId(3), "a.ts", SAMPLE);
        let mut first = Binder::new();
        let mut second = Binder::new();
        build_parsed(&mut first, &parsed);
        build_parsed(&mut second, &parsed);

        let names_of = |binder: &Binder| {
            binder
                .store()
                .iter()
                .map(|symbol| symbol.name.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(names_of(&first), names_of(&second));
        let unresolved_of = |binder: &Binder| {
            binder
                .unresolved()
                .iter()
                .map(|entry| (entry.file.0, entry.name.clone(), entry.count))
                .collect::<Vec<_>>()
        };
        assert_eq!(unresolved_of(&first), unresolved_of(&second));
        assert!(first
            .unresolved()
            .windows(2)
            .all(|pair| pair[0].name <= pair[1].name));
        let sorted: Vec<String> = first
            .store()
            .iter_sorted_by_name()
            .iter()
            .map(|(_, symbol)| symbol.name.clone())
            .collect();
        let mut expected = sorted.clone();
        expected.sort();
        assert_eq!(sorted, expected);
    }

    #[test]
    fn resolve_walks_up_parents() {
        let file = FileId(9);
        let span = Span { file, lo: 0, hi: 1 };
        let scopes = vec![
            ScopeInput {
                index: 0,
                parent: u32::MAX,
            },
            ScopeInput {
                index: 1,
                parent: 0,
            },
        ];
        let symbols = vec![SymbolInput {
            scope: 0,
            name: "y".to_owned(),
            span,
            flags: 0,
        }];
        let mut binder = Binder::new();
        binder.build_file(file, &scopes, &symbols, &[]);
        assert_eq!(binder.resolve(file, 1, "y"), binder.resolve(file, 0, "y"));
        assert!(binder.resolve(file, 1, "y").is_some());
        assert_eq!(binder.resolve(file, 1, "nope"), None);
        assert_eq!(binder.resolve(FileId(10), 0, "y"), None);
    }

    #[test]
    fn inner_scope_shadows_outer() {
        let file = FileId(7);
        let span = Span { file, lo: 0, hi: 1 };
        let scopes = vec![
            ScopeInput {
                index: 0,
                parent: u32::MAX,
            },
            ScopeInput {
                index: 1,
                parent: 0,
            },
        ];
        let symbols = vec![
            SymbolInput {
                scope: 0,
                name: "x".to_owned(),
                span,
                flags: 0,
            },
            SymbolInput {
                scope: 1,
                name: "x".to_owned(),
                span,
                flags: 0,
            },
        ];
        let mut binder = Binder::new();
        binder.build_file(file, &scopes, &symbols, &[]);
        let outer = binder.resolve(file, 0, "x").expect("outer x");
        let inner = binder.resolve(file, 1, "x").expect("inner x");
        assert_ne!(outer, inner);
        assert_eq!(binder.store().len(), 2);
    }
}
