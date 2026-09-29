//! Real-project corpus smoke gate (PITH-P021 follow-up): the pipeline must
//! parse and bind pinned real-world files without panics, with dense scope
//! indices and file-anchored spans throughout.
//!
//! This asserts ROBUSTNESS (no panics, structural invariants, exact fact
//! counts as regression pins) — not checking verdicts: real files sit
//! outside the checking subset (see `corpus/real/coverage-prescan.md`),
//! so every construct here would decline rather than verdict.

use std::time::Instant;

use pith_frontend::parse_module;
use pith_ids::FileId;
use pith_symbols::{Binder, ScopeInput, SymbolInput, UnresolvedInput};

/// One pinned real file: path hint, source, and its regression-pin counts
/// `(scopes, symbols, decls, functions, calls, guards)`.
///
/// Prints `PITH_TIME <path> <ms>` for the parse+bind wall time (P026 timing
/// table input — measurement only, no checker behavior).
fn check_pinned(
    path: &str,
    source: &str,
    file: FileId,
) -> (usize, usize, usize, usize, usize, usize) {
    let started = Instant::now();
    let parsed = parse_module(file, path, source);
    // Dense root-first scope indices (the P012 regression pin).
    let mut seen: Vec<u32> = parsed.scopes.iter().map(|scope| scope.index).collect();
    seen.sort_unstable();
    let want: Vec<u32> = (0..u32::try_from(seen.len()).expect("small corpus")).collect();
    assert_eq!(seen, want, "{path}: scope indices are dense");
    // Every symbol links a real scope; every span anchors this file.
    for symbol in &parsed.symbols {
        assert!(
            (symbol.scope as usize) < parsed.scopes.len(),
            "{path}: symbol '{}' scope {} out of {}",
            symbol.name,
            symbol.scope,
            parsed.scopes.len()
        );
        assert_eq!(symbol.span.file, file, "{path}: symbol span file");
    }
    for decl in &parsed.decls {
        assert!(
            (decl.symbol as usize) < parsed.symbols.len(),
            "{path}: decl symbol out of range"
        );
    }
    // Binding must succeed without panics on real files.
    let mut binder = Binder::new();
    binder.build_file(
        file,
        &parsed
            .scopes
            .iter()
            .map(|scope| ScopeInput {
                index: scope.index,
                parent: scope.parent,
            })
            .collect::<Vec<_>>(),
        &parsed
            .symbols
            .iter()
            .map(|symbol| SymbolInput {
                scope: symbol.scope,
                name: symbol.name.clone(),
                span: symbol.span,
                flags: symbol.flags,
            })
            .collect::<Vec<_>>(),
        &parsed
            .unresolved
            .iter()
            .map(|fact| UnresolvedInput {
                name: fact.name.clone(),
                count: fact.count,
            })
            .collect::<Vec<_>>(),
    );
    assert_eq!(binder.scope_count(file), parsed.scopes.len());
    let counts = (
        parsed.scopes.len(),
        parsed.symbols.len(),
        parsed.decls.len(),
        parsed.functions.len(),
        parsed.calls.len(),
        parsed.guards.len(),
    );
    println!(
        "{path}: scopes={} symbols={} decls={} functions={} calls={} guards={}",
        counts.0, counts.1, counts.2, counts.3, counts.4, counts.5
    );
    println!("PITH_TIME {path} {}", started.elapsed().as_millis());
    counts
}

#[test]
fn real_corpus_parses_and_binds() {
    let defu = check_pinned(
        "defu.ts",
        include_str!("../../../corpus/real/defu/src/defu.ts"),
        FileId(0),
    );
    let utils = check_pinned(
        "_utils.ts",
        include_str!("../../../corpus/real/defu/src/_utils.ts"),
        FileId(1),
    );
    let types = check_pinned(
        "types.ts",
        include_str!("../../../corpus/real/defu/src/types.ts"),
        FileId(2),
    );
    let destr = check_pinned(
        "index.ts",
        include_str!("../../../corpus/real/destr/src/index.ts"),
        FileId(3),
    );
    let plimit = check_pinned(
        "index.d.ts",
        include_str!("../../../corpus/real/plimit-stress/index.d.ts"),
        FileId(4),
    );
    // Exact-count regression pins (captured from the first green remote run;
    // any drift means the frontend changed shape on real files).
    assert_eq!(defu, (18, 27, 6, 2, 12, 0), "defu counts");
    assert_eq!(utils, (6, 3, 1, 1, 0, 0), "utils counts");
    assert_eq!(types, (40, 38, 0, 0, 0, 0), "types counts");
    assert_eq!(destr, (26, 19, 4, 4, 2, 1), "destr counts");
    assert_eq!(plimit, (12, 22, 0, 2, 0, 0), "plimit counts");
}
