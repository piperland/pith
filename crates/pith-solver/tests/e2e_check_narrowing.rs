//! Fact-fed narrowing end-to-end (PITH-P015): the first flow-analysis verdict.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`narrowing_inputs_from_facts`] (the driver: [`DeclFact`](pith_frontend::DeclFact)
//! to [`ConstDecl`]/[`NarrowedUse`, plus guard/decline facts to
//! [`TypeofGuard`]/[`DeclineRegion`]) -> [`check_narrowing`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Driver seams (all disclosed):
//!
//! - Declarations map exactly like `e2e_check_const` (name/scope/symbol from
//!   facts, annotation text verbatim, init kinds per variant).
//! - Uses are the disclosed seam the adapter cannot feed yet (no expression
//!   facts, and the contract scopes the frontend to guard facts only): a
//!   `const` declarator with an annotated [`InitKind::NonLiteral`](pith_frontend::InitKind)
//!   initializer whose fact span slices to a bare identifier becomes a
//!   [`NarrowedUse`] (target = the sliced name, region anchor = the fact
//!   span). Every other shape stays a [`ConstDecl`] and keeps today's
//!   verdicts — including unannotated identifier inits and non-identifier
//!   non-literals.
//! - Unknown targets ride the same driver with no new facts: `declare const
//!   uv: unknown` maps to a [`ConstDecl`] (annotation text verbatim, no
//!   init) and `const a: string = uv` to a [`NarrowedUse`] through the
//!   bare-identifier seam above.
//! - Guards and decline regions map field-for-field (mechanical, exhaustive).
//!
//! Differential rule: oracle lines are `file:TSNNNN: message` plus
//! continuation lines (union elaborations like
//! `  Type 'string' is not assignable …`). The solver mirrors first lines
//! only (the elaboration member choice follows no subset rule — see the
//! solver probe record), so the baseline fold drops non-header lines and the
//! comparison runs on sorted `(numeric-code, first-line-message)` multisets
//! (`TS2322` <-> `PITH2322`) plus the unsupported count. Decline fixtures
//! (complex/nested/non-typeof guards, genuinely-unknown targets) assert the
//! designed divergence instead: zero diagnostics plus recorded decline
//! reasons, with the oracle baseline kept alongside as the record of what
//! was declined.

use pith_frontend::{parse_module, InitKind as FrontendInitKind, ParsedFile};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_narrowing, ConstDecl, DeclKind, DeclineRegion, FileReport, InitKind, NarrowedUse,
    TypeofGuard,
};
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

/// Scope-sensitive fallback span for one declarator, plus its [`SymbolId`].
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

/// Whether a fact span slices to a bare identifier (the disclosed use seam).
fn is_bare_identifier(source: &str, span: Span) -> bool {
    let (lo, hi) = (
        usize::try_from(span.lo).unwrap_or(usize::MAX),
        usize::try_from(span.hi).unwrap_or(0),
    );
    source.get(lo..hi).is_some_and(|text| {
        !text.is_empty()
            && text
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
    })
}

/// Fact-fed narrowing inputs, bundled so the driver signature stays lean.
struct NarrowingDriverOut {
    decls: Vec<ConstDecl>,
    uses: Vec<NarrowedUse>,
    guards: Vec<TypeofGuard>,
    declines: Vec<DeclineRegion>,
}

/// The fact-fed narrowing driver: declarations, identifier-uses, guards, and
/// decline regions from adapter facts plus the disclosed identifier slice.
fn narrowing_inputs_from_facts(
    source: &str,
    parsed: &ParsedFile,
    binder: &Binder,
) -> NarrowingDriverOut {
    let mut decls = Vec::new();
    let mut uses = Vec::new();
    for decl in &parsed.decls {
        let (name, span, symbol) = fallback_span(parsed, binder, decl.symbol, decl.scope);
        let annotation = decl.annotation.as_ref().map(|ann| ann.text.clone());
        let init = decl.init.as_ref().map(|init| map_init(init.kind));
        let init_span = decl.init.as_ref().map(|init| init.span);
        // Disclosed seam: annotated bare-identifier inits are narrowing uses.
        if let (Some(text), Some(init_span)) = (annotation.clone(), init_span) {
            if init == Some(InitKind::NonLiteral) && is_bare_identifier(source, init_span) {
                let (lo, hi) = (
                    usize::try_from(init_span.lo).unwrap_or(usize::MAX),
                    usize::try_from(init_span.hi).unwrap_or(0),
                );
                uses.push(NarrowedUse {
                    name,
                    span,
                    scope: decl.scope,
                    symbol,
                    annotation: text,
                    target: source.get(lo..hi).expect("sliced identifier").to_owned(),
                    init_span,
                });
                continue;
            }
        }
        decls.push(ConstDecl {
            name,
            span,
            scope: decl.scope,
            symbol,
            kind: DeclKind::Const,
            annotation,
            init,
            init_ident: None,
            init_object: None,
            // No array-member facts yet (see the check-functions driver).
            init_array: None,
            cast: None,
            init_ternary: None,
            init_member_ref: None,
        });
    }
    let guards = parsed
        .guards
        .iter()
        .map(|guard| TypeofGuard {
            target: guard.target.clone(),
            matched: guard.matched.clone(),
            negated: guard.negated,
            then_span: guard.then_span,
            else_span: guard.else_span,
            early_return: guard.early_return,
            if_span: guard.if_span,
        })
        .collect();
    let declines = parsed
        .decline_regions
        .iter()
        .map(|region| DeclineRegion {
            span: region.span,
            reason: region.reason.clone(),
        })
        .collect();
    NarrowingDriverOut {
        decls,
        uses,
        guards,
        declines,
    }
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
    let inputs = narrowing_inputs_from_facts(source, &parsed, &binder);
    let mut db = QueryDb::new();
    let facts = pith_solver::NarrowingFacts {
        uses: &inputs.uses,
        guards: &inputs.guards,
        declines: &inputs.declines,
    };
    check_narrowing(FILE, &inputs.decls, &facts, &binder, &mut db)
}

/// Parses normalized oracle HEADER lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs, folding away continuation lines (the
/// union elaborations the solver mirrors only by first line — see the module
/// docs).
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = expected
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| {
            let mut parts = line.splitn(3, ':');
            let _file = parts.next()?;
            let code = parts.next()?.trim().to_owned();
            let message = parts.next()?.trim().to_owned();
            if code.len() > 2
                && code.starts_with("TS")
                && code[2..].chars().all(|c| c.is_ascii_digit())
            {
                Some((code, message))
            } else {
                None
            }
        })
        .collect();
    out.sort();
    out
}

/// Asserts the pipeline verdict differentially equals the recorded baseline:
/// same `(code-family, first-line-message)` multiset (`TS`/`PITH` prefixes
/// folded) and the expected unsupported count, with sane anchored spans.
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

/// Asserts the designed decline: zero diagnostics (even where the oracle
/// diagnoses — the baseline is the record of what was declined) plus the
/// expected unsupported count with recorded reasons.
fn expect_declined(name: &str, source: &str, unsupported: usize) {
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "{name}: decline must stay silent: {:?}",
        report.diagnostics
    );
    let unsupported_notes = &report.unsupported;
    assert_eq!(
        report.unsupported.len(),
        unsupported,
        "{name}: unsupported count: {unsupported_notes:?}"
    );
    for note in &report.unsupported {
        assert_eq!(note.file, FILE, "{name}: unsupported file");
        assert!(note.span.lo < note.span.hi, "{name}: degenerate span");
        assert!(!note.reason.is_empty(), "{name}: empty decline reason");
    }
}

macro_rules! refine_test {
    ($test:ident, $source:literal, $expected:literal, $unsupported:expr) => {
        #[test]
        fn $test() {
            expect_differential(
                stringify!($test),
                include_str!(concat!("../../../corpus/check-narrowing/", $source)),
                include_str!(concat!("../../../corpus/check-narrowing/", $expected)),
                $unsupported,
            );
        }
    };
}

macro_rules! decline_test {
    ($test:ident, $source:literal, $unsupported:expr) => {
        #[test]
        fn $test() {
            expect_declined(
                stringify!($test),
                include_str!(concat!("../../../corpus/check-narrowing/", $source)),
                $unsupported,
            );
        }
    };
}

refine_test!(
    guarded_match_is_silent,
    "guarded-match.ts",
    "guarded-match.expected.txt",
    1
);
refine_test!(
    guarded_mismatch_matches_ts2322,
    "guarded-mismatch.ts",
    "guarded-mismatch.expected.txt",
    1
);
refine_test!(
    unguarded_mismatch_matches_ts2322_first_line,
    "unguarded-mismatch.ts",
    "unguarded-mismatch.expected.txt",
    1
);
refine_test!(
    else_branch_matches_ts2322,
    "else-branch.ts",
    "else-branch.expected.txt",
    1
);
refine_test!(
    early_return_matches_ts2322,
    "early-return.ts",
    "early-return.expected.txt",
    1
);
refine_test!(
    unknown_unguarded_matches_ts2322_unknown_spelling,
    "unknown-unguarded.ts",
    "unknown-unguarded.expected.txt",
    1
);
refine_test!(
    unknown_guarded_match_is_silent,
    "unknown-guarded-match.ts",
    "unknown-guarded-match.expected.txt",
    1
);
refine_test!(
    unknown_guarded_mismatch_matches_ts2322,
    "unknown-guarded-mismatch.ts",
    "unknown-guarded-mismatch.expected.txt",
    1
);
refine_test!(
    unknown_to_unknown_is_silent,
    "unknown-to-unknown.ts",
    "unknown-to-unknown.expected.txt",
    1
);
decline_test!(complex_guard_is_declined, "complex-guard.ts", 2);
decline_test!(nested_guard_is_declined, "nested-guard.ts", 2);
decline_test!(nontypeof_guard_is_declined, "nontypeof-guard.ts", 2);
decline_test!(
    genuinely_unknown_is_declined,
    "unknown-genuinely-unknown.ts",
    2
);

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-narrowing/else-branch.ts");
    let first = run_pipeline(source);
    let second = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_routes_uses_and_decls_without_hand_feeding() {
    // Guards the routing itself: literal inits stay declarations,
    // bare-identifier inits become uses, guards/declines map 1:1.
    let source = "declare const x: number | string;\n\
                  const ok: string = \"lit\";\n\
                  if (typeof x === \"string\") {\n  const use: string = x;\n}\n";
    let parsed = parse_module(FILE, "m.ts", source);
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder(&parsed);
    let inputs = narrowing_inputs_from_facts(source, &parsed, &binder);
    let decls = &inputs.decls;
    let uses = &inputs.uses;
    let guards = &inputs.guards;
    let declines = &inputs.declines;
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "x");
    assert_eq!(decls[1].name, "ok");
    assert_eq!(decls[1].init, Some(InitKind::String));
    assert_eq!(uses.len(), 1);
    assert_eq!(uses[0].name, "use");
    assert_eq!(uses[0].target, "x");
    assert_eq!(uses[0].annotation, "string");
    assert_eq!(guards.len(), 1);
    assert_eq!(guards[0].target, "x");
    assert!(declines.is_empty());
}
