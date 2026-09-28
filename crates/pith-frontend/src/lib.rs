//! Pith frontend adapter (Oxc boundary).
//!
//! Provenance: Oxc 0.152.0 (MIT), oxc-project/oxc. Re-checked 2026-09-28:
//! 0.152.0 is still the latest 0.15x on crates.io, so no bump. Exact `=`
//! pins + Cargo.lock committed.
//!
//! Boundary law: everything Oxc-typed dies inside [`parse_module`]. Callers
//! receive only Pith-owned facts keyed by [`FileId`]. No `oxc_*` type may
//! appear in any other `pith-*` crate's public API.
//!
//! Declaration facts (P010): [`ParsedFile::decls`] carries one [`DeclFact`]
//! per `const` declarator with a simple identifier binding, pairing the
//! annotation text and span ([`AnnotationFact`]) with the initializer
//! literal kind and span ([`InitFact`]/[`InitKind`]). Each fact keys to its
//! owning [`SymbolFact`] by per-file symbol index. These replace the
//! solver's hand-fed `ConstDecl` seam (the `DeclAnnotationFact` plus
//! `InitLiteralFact` BLOCKER in `pith-solver`).
//!
//! Build-mode decision (P010): the declarator walk uses
//! `oxc_ast_visit::Visit` over the already-parsed program — NOT
//! `SemanticBuilder::with_build_nodes(true)`. Rationale: declarators are
//! purely syntactic, so the visitor reaches every one (top level, nested
//! blocks/functions, `export const`, `for(const ... of ...)`) with a single
//! O(n) pass and zero change to the semantic build; enabling `AstNodes`
//! would materialize a node arena plus parent maps for every file just to
//! rediscover the same declarators. Measurement: no local Rust toolchain is
//! available to this task (CTO verifies remotely on E2B), so the
//! with/without-`AstNodes` semantic-build delta is recorded as unknown; the
//! semantic-build configuration is unchanged by this task, and the added
//! cost is one linear visitor pass. Destructured bindings (`const {a} = …`)
//! bind many symbols per declarator and are skipped — outside the solver
//! subset, never silently mis-keyed.

use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, Expression, Program, VariableDeclaration, VariableDeclarationKind,
    VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::{GetSpan, SourceType};
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

/// Annotation on one `const` declarator: raw type text plus its span.
///
/// `span` is the raw `TSTypeAnnotation` range (colon-inclusive: `: number`
/// spans the colon through the type). `text` is the source slice of that
/// range with the leading colon stripped (`"number"`, `"number | string"`),
/// so it feeds the solver's annotation map (and its `'|'` union check)
/// directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnotationFact {
    pub text: String,
    pub span: Span,
}

/// Initializer literal kind, mirroring the solver's subset.
///
/// Only primitive literals are classifiable. Anything else (`other`,
/// `{...}`, `f()`, `` `tpl` ``, `-1`, …) is [`InitKind::NonLiteral`] —
/// expression facts the adapter does not emit yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitKind {
    /// A numeric literal (`1`, `0x10`, …).
    Number,
    /// A string literal (`"ok"`, …).
    String,
    /// `true` / `false`.
    Boolean,
    /// `null`.
    Null,
    /// The `undefined` identifier.
    Undefined,
    /// Any non-literal initializer (identifier, object, call, …).
    NonLiteral,
}

/// Initializer on one `const` declarator: literal kind plus span.
///
/// `span` is the initializer expression's own range (`None` on
/// [`DeclFact::init`] means no initializer at all, e.g. `declare const`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitFact {
    pub kind: InitKind,
    pub span: Span,
}

/// One `const` declarator's declaration facts, keyed to its symbol.
///
/// `symbol` is the per-file index into [`ParsedFile::symbols`] of the
/// [`SymbolFact`] for the same declarator (matched on binding name +
/// binding start; declaration order in [`ParsedFile::decls`] is source
/// order). Only simple-identifier bindings produce facts; destructured
/// declarators are skipped (see the module-level build-mode note).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclFact {
    /// Per-file symbol index of the declarator's binding.
    pub symbol: u32,
    /// Raw annotation text + span; `None` means unannotated.
    pub annotation: Option<AnnotationFact>,
    /// Initializer literal kind + span; `None` means no initializer.
    pub init: Option<InitFact>,
}

/// Everything Pith owns after a frontend pass. Arenas are dropped on return.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    pub file: FileId,
    pub scopes: Vec<ScopeFact>,
    pub symbols: Vec<SymbolFact>,
    pub unresolved: Vec<UnresolvedFact>,
    pub imports: Vec<ImportFact>,
    /// One fact per `const` declarator (identifier bindings only), in
    /// source order. Empty when the file declares no consts.
    pub decls: Vec<DeclFact>,
    /// Parser + semantic diagnostics as plain strings (codes deferred to P008).
    pub errors: Vec<String>,
}

// Gap (P005, narrowed by P010): declaration facts (`decls`) are now present;
// per-reference spans still need AstNodes — v1 records counts + names.
// Freshness-relevant occurrence identity will key off NodeId in P005/P006.

// Byte slice of `source` at an Oxc span, or `None` when out of bounds
// (defensive only: spans the parser hands us always slice cleanly).
fn slice_at(source: &str, span: oxc_span::Span) -> Option<&str> {
    let lo = usize::try_from(span.start).ok()?;
    let hi = usize::try_from(span.end).ok()?;
    source.get(lo..hi)
}

/// Targeted `const`-declarator collector: a syntactic [`Visit`] pass, so no
/// `AstNodes` store is built (see the module-level build-mode note). All
/// facts are Pith-owned; nothing borrowed escapes the pass.
#[derive(Debug)]
struct DeclCollector<'a> {
    file: FileId,
    source: &'a str,
    /// `(binding name, binding start)` -> per-file symbol index. Keyed on
    /// the start (not the full span) so ESTree-style annotation-extended
    /// ranges can never mis-key; `(name, start)` is injective — one token,
    /// one binding.
    symbols: std::collections::HashMap<(String, u32), u32>,
    decls: Vec<DeclFact>,
}

impl DeclCollector<'_> {
    /// Records one declarator when it is a `const` identifier binding.
    /// Destructured patterns bind many symbols and are skipped.
    fn record_declarator(&mut self, declarator: &VariableDeclarator<'_>) {
        let BindingPattern::BindingIdentifier(binding) = &declarator.id else {
            return;
        };
        let name = slice_at(self.source, binding.span);
        let Some(name) = name else { return };
        let Some(&symbol) = self.symbols.get(&(name.to_owned(), binding.span.start)) else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };

        let annotation = declarator.type_annotation.as_ref().and_then(|ann| {
            let raw = slice_at(self.source, ann.span)?;
            Some(AnnotationFact {
                text: raw.trim_start_matches(':').trim().to_owned(),
                span: Span {
                    file: self.file,
                    lo: ann.span.start,
                    hi: ann.span.end,
                },
            })
        });

        let init = declarator.init.as_ref().map(|expression| {
            let span = expression.span();
            let kind = match expression {
                Expression::NumericLiteral(_) => InitKind::Number,
                Expression::StringLiteral(_) => InitKind::String,
                Expression::BooleanLiteral(_) => InitKind::Boolean,
                Expression::NullLiteral(_) => InitKind::Null,
                Expression::Identifier(ident) => {
                    if slice_at(self.source, ident.span).is_some_and(|text| text == "undefined") {
                        InitKind::Undefined
                    } else {
                        InitKind::NonLiteral
                    }
                }
                _ => InitKind::NonLiteral,
            };
            InitFact {
                kind,
                span: Span {
                    file: self.file,
                    lo: span.start,
                    hi: span.end,
                },
            }
        });

        self.decls.push(DeclFact {
            symbol,
            annotation,
            init,
        });
    }
}

impl<'a> Visit<'a> for DeclCollector<'a> {
    fn visit_variable_declaration(&mut self, it: &VariableDeclaration<'a>) {
        if matches!(it.kind, VariableDeclarationKind::Const) {
            for declarator in &it.declarations {
                self.record_declarator(declarator);
            }
        }
        // Keep walking: initializers may nest functions/blocks that declare
        // their own consts (`const f = () => { const y = 1; … }`).
        walk::walk_variable_declaration(self, it);
    }
}

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

    // Symbols + resolved references. Scope linkage uses the SAME per-file
    // re-indexing as ScopeFact.index (never the raw Oxc ScopeId number).
    let mut symbols = Vec::new();
    for symbol_id in scoping.symbol_ids() {
        let refs = scoping.get_resolved_reference_ids(symbol_id);
        let mut names: Vec<String> = refs
            .iter()
            .filter_map(|r| scoping.get_reference_name(*r).map(str::to_owned))
            .collect();
        names.sort();
        names.dedup();
        let scope = scope_index_of
            .get(&scoping.symbol_scope_id(symbol_id))
            .copied()
            .unwrap_or(u32::MAX);
        symbols.push(SymbolFact {
            index: sat_u32(symbols.len()),
            scope,
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

    let decls = collect_decls(file, source, &parse.program, &symbols);
    ParsedFile {
        file,
        scopes,
        symbols,
        unresolved,
        imports,
        decls,
        errors,
    }
}

/// Runs the targeted `const`-declarator walk and returns owned facts.
///
/// Symbol linkage resolves each declarator's `(name, binding start)` to the
/// per-file [`SymbolFact`] index built above; facts come out in source
/// (visitor) order, so the sequence is deterministic.
fn collect_decls<'a>(
    file: FileId,
    source: &'a str,
    program: &Program<'a>,
    symbols: &[SymbolFact],
) -> Vec<DeclFact> {
    let mut index_of = std::collections::HashMap::new();
    for symbol in symbols {
        let previous = index_of.insert((symbol.name.clone(), symbol.span.lo), symbol.index);
        debug_assert!(
            previous.is_none(),
            "duplicate (name, binding-start) symbol key"
        );
    }
    let mut collector = DeclCollector {
        file,
        source,
        symbols: index_of,
        decls: Vec::new(),
    };
    collector.visit_program(program);
    collector.decls
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

    #[test]
    fn scope_indices_are_dense_and_linked() {
        let src = "const x = 1;\nfunction f(a: string) {\n  const y = a + String(x);\n  function g() { return y; }\n}\n";
        let pf = parse_module(FileId(4), "n.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let len = sat_u32(pf.scopes.len());
        // every symbol points at a real scope; every parent resolves or is root
        for symbol in &pf.symbols {
            assert!(
                symbol.scope < len,
                "symbol {} scope {} out of {}",
                symbol.name,
                symbol.scope,
                len
            );
        }
        for scope in &pf.scopes {
            assert!(
                scope.parent == u32::MAX || scope.parent < len,
                "scope {} parent {} out of {}",
                scope.index,
                scope.parent,
                len
            );
        }
        // parent chains terminate at the root within len steps
        for scope in &pf.scopes {
            let mut at = scope.index;
            for _ in 0..len {
                if at == u32::MAX {
                    break;
                }
                at = pf.scopes[usize::try_from(at).expect("dense scope index")].parent;
            }
            assert_eq!(
                at,
                u32::MAX,
                "scope {} chain does not terminate",
                scope.index
            );
        }
    }
}
