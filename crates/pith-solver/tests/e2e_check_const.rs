//! Fact-fed solver end-to-end (PITH-P011): the first true pipeline verdict.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`decls_from_facts`] (the driver: [`DeclFact`](pith_frontend::DeclFact)
//! to [`ConstDecl`], zero hand-feeding) -> [`check_file`] -> [`FileReport`],
//! then a differential against the recorded tsc `.expected.txt` baselines.
//!
//! Driver placement rationale: this integration test IS the driver. A
//! `src/driver` module would either add a runtime `pith-frontend` dependency
//! (a layering inversion: Oxc-tainted facts flowing into the solver API) or
//! be `cfg(test)`-gated anyway, gaining nothing over `tests/`. The
//! dev-dependency mirrors `pith-symbols`' existing test-only frontend
//! adaptation, so the boundary law holds and `check_file` core is untouched.
//!
//! Differential rule: oracle lines are `file:TSNNNN: message`; spans are
//! intentionally discarded (line/col shift with comment edits, per the oracle
//! harness). Comparison is on sorted `(numeric-code, message)` multisets —
//! `TS2322` <-> `PITH2322`, `TS2304` <-> `PITH2304` — plus the unsupported
//! count for out-of-subset fixtures.
//!
//! Scope-sensitivity (P012): the driver resolves every fallback span
//! scope-sensitively (`DeclFact.symbol` -> `SymbolFact.scope` ->
//! [`Binder::resolve`] -> store span) AND threads that scope plus the
//! resolved [`SymbolId`] into each [`ConstDecl`], so `check_file`'s internal
//! span resolution agrees with the driver even when two same-name decls
//! share a file. No check-const fixture shadows a name; the shadowing proof
//! lives in the solver unit tests (`shadowed_same_name_verdicts_against_own_scopes`).

use pith_frontend::{parse_module, InitKind as FrontendInitKind, ParsedFile};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{check_file, ConstDecl, DeclKind, FileReport, InitKind};
use pith_symbols::{Binder, ScopeInput, SymbolInput, UnresolvedInput};

const FILE: FileId = FileId(0);

/// Builds a fresh binder from one parsed file's scope/symbol/unresolved facts.
fn build_binder(parsed: &ParsedFile) -> Binder {
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
    let mut binder = Binder::new();
    binder.build_file(parsed.file, &scopes, &symbols, &unresolved);
    binder
}

/// Maps one frontend initializer kind to the solver's, variant by variant.
///
/// Both enums carry the same six shapes; the match is exhaustive so a new
/// frontend variant fails to compile here instead of silently mis-checking.
fn map_init(kind: FrontendInitKind) -> InitKind {
    match kind {
        FrontendInitKind::Number => InitKind::Number,
        FrontendInitKind::String => InitKind::String,
        FrontendInitKind::Boolean => InitKind::Boolean,
        FrontendInitKind::Null => InitKind::Null,
        FrontendInitKind::Undefined => InitKind::Undefined,
        FrontendInitKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Scope-sensitive fallback span for one declarator: `decl.symbol` indexes
/// `ParsedFile.symbols`, and the `(scope, name)` pair resolves through the
/// binder to the exact declaration span plus its [`SymbolId`]. The scope
/// comes from the new [`DeclFact`](pith_frontend::DeclFact) scope fact;
/// spans fall back to the binding span only when the binder cannot resolve
/// (never happens for well-formed facts).
fn fallback_span(
    parsed: &ParsedFile,
    binder: &Binder,
    symbol_index: u32,
    scope: u32,
) -> (String, Span, Option<SymbolId>) {
    let symbol = &parsed.symbols[usize::try_from(symbol_index).expect("dense symbol index")];
    let id = binder.resolve(parsed.file, scope, &symbol.name);
    let span = id
        .and_then(|id| binder.store().get(id))
        .map_or(symbol.span, |found| found.span);
    (symbol.name.clone(), span, id)
}

/// The fact-fed driver: every [`ConstDecl`] field comes from adapter facts.
///
/// - `name` via `ParsedFile.symbols[decl.symbol]` (never re-typed);
/// - `scope`/`symbol` via the declarator scope fact plus binder resolution;
/// - `kind` is `const` (the adapter emits no `let` facts yet);
/// - `annotation` as the frontend's colon-stripped text verbatim;
/// - `init` via the explicit [`map_init`] variant map;
/// - `init_object` is `None` (no `ObjectMemberFact`s yet; check-const
///   fixtures hold no object literals anyway).
fn decls_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<ConstDecl> {
    parsed
        .decls
        .iter()
        .map(|decl| {
            let (name, span, symbol) = fallback_span(parsed, binder, decl.symbol, decl.scope);
            ConstDecl {
                name,
                span,
                scope: decl.scope,
                symbol,
                kind: DeclKind::Const,
                annotation: decl.annotation.as_ref().map(|ann| ann.text.clone()),
                init: decl.init.as_ref().map(|init| map_init(init.kind)),
                init_object: None,
                cast: None,
            }
        })
        .collect()
}

/// Runs the full real pipeline on one source text with a fresh binder and db.
fn run_pipeline(source: &str) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = decls_from_facts(&parsed, &binder);
    let mut db = QueryDb::new();
    check_file(FILE, &decls, &binder, &mut db)
}

/// Parses normalized oracle lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs; spans/positions are already folded away.
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = expected
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let mut parts = line.splitn(3, ':');
            let _file = parts.next().unwrap_or("");
            let code = parts.next().unwrap_or("").trim().to_owned();
            let message = parts.next().unwrap_or("").trim().to_owned();
            (code, message)
        })
        .collect();
    out.sort();
    out
}

/// Asserts the pipeline verdict differentially equals the recorded baseline:
/// same `(code-family, message)` multiset (`TS`/`PITH` prefixes folded) and
/// the expected unsupported count, with sane anchored spans throughout.
fn expect_differential(name: &str, source: &str, expected: &str, unsupported: usize) {
    let report = run_pipeline(source);
    let mut actual: Vec<(String, String)> = report
        .diagnostics
        .iter()
        .map(|diag| {
            let family = diag
                .code
                .strip_prefix("PITH")
                .unwrap_or(diag.code.as_str())
                .to_owned();
            (format!("TS{family}"), diag.message.clone())
        })
        .collect();
    actual.sort();
    let want = parse_baseline(expected);
    assert_eq!(
        actual, want,
        "{name}: pipeline diagnostics diverge from oracle baseline"
    );
    let unsupported_notes = &report.unsupported;
    assert_eq!(
        report.unsupported.len(),
        unsupported,
        "{name}: unsupported count: {unsupported_notes:?}"
    );
    for diag in &report.diagnostics {
        assert_eq!(diag.file, FILE, "{name}: diagnostic file");
        assert!(diag.span.lo < diag.span.hi, "{name}: degenerate span");
    }
    for note in &report.unsupported {
        assert_eq!(note.file, FILE, "{name}: unsupported file");
        assert!(note.span.lo < note.span.hi, "{name}: degenerate span");
    }
}

macro_rules! fixture_test {
    ($test:ident, $source:literal, $expected:literal, $unsupported:expr) => {
        #[test]
        fn $test() {
            expect_differential(
                stringify!($test),
                include_str!(concat!("../../../corpus/check-const/", $source)),
                include_str!(concat!("../../../corpus/check-const/", $expected)),
                $unsupported,
            );
        }
    };
}

fixture_test!(
    annotated_correct_is_silent,
    "annotated-correct.ts",
    "annotated-correct.expected.txt",
    0
);
fixture_test!(
    mismatch_number_matches_ts2322,
    "mismatch-number.ts",
    "mismatch-number.expected.txt",
    0
);
fixture_test!(
    mismatch_string_matches_ts2322,
    "mismatch-string.ts",
    "mismatch-string.expected.txt",
    0
);
fixture_test!(
    mismatch_boolean_matches_ts2322,
    "mismatch-boolean.ts",
    "mismatch-boolean.expected.txt",
    0
);
fixture_test!(
    unknown_annotation_matches_ts2304,
    "unknown-annotation.ts",
    "unknown-annotation.expected.txt",
    0
);
fixture_test!(
    multi_declarator_matches_ts2322,
    "multi-declarator.ts",
    "multi-declarator.expected.txt",
    0
);
fixture_test!(
    union_annotation_is_unsupported,
    "union-annotation.ts",
    "union-annotation.expected.txt",
    1
);
fixture_test!(
    no_annotation_is_unsupported,
    "no-annotation.ts",
    "no-annotation.expected.txt",
    1
);

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-const/multi-declarator.ts");
    let first = run_pipeline(source);
    let second = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names come from symbol linkage, annotation
    // text is verbatim, init kinds map per variant, spans anchor to the file.
    let parsed = parse_module(FILE, "m.ts", "const a: number = 1, b = x;\n");
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.decls.len(), 2);
    let binder = build_binder(&parsed);
    let decls = decls_from_facts(&parsed, &binder);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "a");
    assert_eq!(decls[0].annotation.as_deref(), Some("number"));
    assert_eq!(decls[0].init, Some(InitKind::Number));
    assert_eq!(decls[0].kind, DeclKind::Const);
    assert_eq!(decls[0].init_object, None);
    assert!(decls[0].symbol.is_some(), "driver resolves the SymbolId");
    assert_eq!(
        decls[0].scope,
        parsed.symbols[usize::try_from(parsed.decls[0].symbol).expect("dense")].scope
    );
    assert_eq!(decls[1].name, "b");
    assert_eq!(decls[1].annotation, None);
    assert_eq!(decls[1].init, Some(InitKind::NonLiteral));
    for decl in &decls {
        assert_eq!(decl.span.file, FILE);
        assert!(decl.span.lo < decl.span.hi);
    }
}
