//! Pith frontend adapter (Oxc boundary).
//!
//! Provenance: Oxc 0.152.0 (MIT), oxc-project/oxc. Re-check latest 0.15x at
//! each kickoff; exact pins + Cargo.lock committed.
//!
//! Boundary law: everything Oxc-typed dies inside [`parse_module`]. Callers
//! receive only Pith-owned facts keyed by [`FileId`]. No `oxc_*` type may
//! appear in any other `pith-*` crate's public API.

use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use pith_ids::{FileId, Span};

/// Saturating `usize` -> `u32` for per-file fact indices (files never approach
/// 4B facts; saturation beats silent truncation).
#[inline]
#[must_use]
fn sat_u32(v: usize) -> u32 {
    u32::try_from(v).unwrap_or(u32::MAX)
}

/// One lexical scope, indexed per file (position in [`ParsedFile::scopes`]).
#[derive(Clone, Debug)]
pub struct ScopeFact {
    /// Per-file scope index; root scope is always index 0.
    pub index: u32,
    /// Parent scope index, or `u32::MAX` for the root.
    pub parent: u32,
    /// Raw `ScopeFlags` bits (opaque to Pith core; interpreted at boundary).
    pub flags: u32,
}

/// One bound symbol, indexed per file (position in [`ParsedFile::symbols`]).
#[derive(Clone, Debug)]
pub struct SymbolFact {
    /// Per-file symbol index.
    pub index: u32,
    /// Owning scope (per-file scope index).
    pub scope: u32,
    pub name: String,
    pub span: Span,
    /// Raw `SymbolFlags` bits.
    pub flags: u32,
    /// Number of resolved references (spans deferred; see gap note below).
    pub resolved_ref_count: u32,
    /// Names of resolved references (debug/audit aid).
    pub resolved_ref_names: Vec<String>,
}

/// Unresolved (global or undeclared) reference name + occurrence count.
#[derive(Clone, Debug)]
pub struct UnresolvedFact {
    pub name: String,
    pub count: u32,
}

/// Import specifier with its span.
#[derive(Clone, Debug)]
pub struct ImportFact {
    pub specifier: String,
    pub span: Span,
}

/// Everything Pith owns after a frontend pass. Arenas are dropped on return.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    pub file: FileId,
    pub scopes: Vec<ScopeFact>,
    pub symbols: Vec<SymbolFact>,
    pub unresolved: Vec<UnresolvedFact>,
    pub imports: Vec<ImportFact>,
    /// Parser + semantic diagnostics as plain strings (codes deferred to P008).
    pub errors: Vec<String>,
}

// Gap (P005): per-reference spans need AstNodes; v1 records counts + names.
// Freshness-relevant occurrence identity will key off NodeId in P005/P006.

/// Parse TypeScript source into Pith-owned facts.
///
/// `path_hint` (e.g. `"a.ts"`, `"b.tsx"`) selects module/script + JSX; only
/// the suffix behavior crosses the boundary, never Oxc types.
#[must_use]
pub fn parse_module(file: FileId, path_hint: &str, source: &str) -> ParsedFile {
    let allocator = Allocator::default();
    let source_type = SourceType::from_path(path_hint).unwrap_or_default();
    let parse = Parser::new(&allocator, source, source_type).parse();

    let mut errors: Vec<String> = parse.diagnostics.iter().map(|e| format!("{e:?}")).collect();

    let semantic = SemanticBuilder::new().build(&parse.program);
    errors.extend(semantic.diagnostics.iter().map(|e| format!("{e:?}")));
    let scoping = semantic.semantic.scoping();

    let span_of = |s: oxc_span::Span| Span {
        file,
        lo: s.start,
        hi: s.end,
    };

    // Scopes: descendants-from-root is root-first; re-index per file.
    let mut scope_index_of = std::collections::HashMap::new();
    let mut scopes = Vec::new();
    for scope_id in scoping.scope_descendants_from_root() {
        let index = sat_u32(scopes.len());
        scope_index_of.insert(scope_id, index);
    }
    for scope_id in scoping.scope_descendants_from_root() {
        let index = scope_index_of[&scope_id];
        let parent = scoping
            .scope_parent_id(scope_id)
            .and_then(|p| scope_index_of.get(&p).copied())
            .unwrap_or(u32::MAX);
        scopes.push(ScopeFact {
            index,
            parent,
            flags: u32::from(scoping.scope_flags(scope_id).bits()),
        });
    }

    // Symbols + resolved references.
    let mut symbols = Vec::new();
    for symbol_id in scoping.symbol_ids() {
        let refs = scoping.get_resolved_reference_ids(symbol_id);
        let mut names: Vec<String> = refs
            .iter()
            .filter_map(|r| scoping.get_reference_name(*r).map(str::to_owned))
            .collect();
        names.sort();
        names.dedup();
        symbols.push(SymbolFact {
            index: sat_u32(symbols.len()),
            scope: scoping
                .symbol_scope_id(symbol_id)
                .index()
                .try_into()
                .unwrap_or(u32::MAX),
            name: scoping.symbol_name(symbol_id).to_owned(),
            span: span_of(scoping.symbol_span(symbol_id)),
            flags: scoping.symbol_flags(symbol_id).bits(),
            resolved_ref_count: sat_u32(refs.len()),
            resolved_ref_names: names,
        });
    }

    // Root unresolved references. Names live in the map KEYS: `Reference`
    // carries no name and `get_reference_name` resolves via symbol (None here).
    let mut unresolved = Vec::new();
    for (name, ids) in scoping.root_unresolved_references() {
        unresolved.push(UnresolvedFact {
            name: name.as_str().to_owned(),
            count: sat_u32(ids.len()),
        });
    }
    unresolved.sort_by(|a, b| a.name.cmp(&b.name));

    // Module record: import specifiers.
    let imports = parse
        .module_record
        .import_entries
        .iter()
        .map(|e| ImportFact {
            specifier: e.module_request.name.to_string(),
            span: span_of(e.module_request.span),
        })
        .collect();

    ParsedFile {
        file,
        scopes,
        symbols,
        unresolved,
        imports,
        errors,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
import { b } from "./b";
const x: number = 1;
export function f(a: string): string { return a + b; }
"#;

    #[test]
    fn adapter_extracts_boundary_facts() {
        let pf = parse_module(FileId(0), "a.ts", SAMPLE);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // root scope + module scope at minimum
        assert!(!pf.scopes.is_empty());
        assert_eq!(pf.scopes[0].parent, u32::MAX);
        let names: Vec<&str> = pf.symbols.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"x"), "symbols: {names:?}");
        assert!(names.contains(&"f"), "symbols: {names:?}");
        // all spans anchored to our file
        assert!(pf.symbols.iter().all(|s| s.span.file == FileId(0)));
        // import specifier captured with span
        assert_eq!(pf.imports.len(), 1);
        assert_eq!(pf.imports[0].specifier, "./b");
        assert_eq!(pf.imports[0].span.file, FileId(0));
    }

    #[test]
    fn unresolved_globals_reported() {
        let pf = parse_module(FileId(1), "g.ts", "console.log(missing);\n");
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let names: Vec<&str> = pf.unresolved.iter().map(|u| u.name.as_str()).collect();
        assert!(names.contains(&"console"), "unresolved: {names:?}");
        assert!(names.contains(&"missing"), "unresolved: {names:?}");
    }
}
